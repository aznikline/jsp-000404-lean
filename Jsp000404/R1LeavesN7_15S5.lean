import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6784000 in
set_option maxHeartbeats 6784000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s5 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3207 | h3207
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3208 | h3208
      · linarith only [h3208, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3210 | h3210
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3211 | h3211
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3212 | h3212
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3213 | h3213
              · linarith only [h0, h3213, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3215 | h3215
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3216 | h3216
                  · linarith only [h1, h3208, h3216, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3218 | h3218
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3219 | h3219
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3220 | h3220
                        · linarith only [h0, h1, h3208, h3212, h3220, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3222 | h3222
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3223 | h3223
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3224 | h3224
                              · rcases h0bigk with h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c | h3225c
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3222, h3224, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h1, h3212, h3222, h3224, hc01, hc45, hlam, hphi, ht0b, ht5b, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3222, h3224, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  rcases p3225_3 (m.d 0 1) (by simp) with h3230 | h3230
                                  · rcases p3225_3 (m.d 0 2) (by simp) with h3231 | h3231
                                    · linarith only [h0, h3231, hlam]
                                    · linarith only [h3207, h3231, hlam]
                                  · linarith only [h3, h3230, hlam]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h0, hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h1, h3212, h3222, h3224, hc02, hc45, hlam, hphi, ht0b, ht5b, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h5, hlam, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3220, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h1, hlam, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h4, hlam, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3208, hlam, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3, h3215, h3220, h3222, h3224, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h2, hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3220, h5, hc02, hc34, hlam, hphi, ht23, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3220, h5, hc03, hc34, hlam, hphi, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  rcases p3225_3 (m.d 0 1) (by simp) with h3249 | h3249
                                  · rcases p3225_3 (m.d 0 2) (by simp) with h3250 | h3250
                                    · linarith only [h3250, h5, hlam]
                                    · linarith only [h3207, h3250, hlam]
                                  · linarith only [h3, h3249, hlam]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3, hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3207, hlam, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3210, hlam, p3225_0]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [h3211, hlam, p3225_1]
                                · have p3225_0 := h3225c.1
                                  have p3225_1 := h3225c.2.1
                                  have p3225_2 := h3225c.2.2.1
                                  have p3225_3 := h3225c.2.2.2
                                  linarith only [hlam, p3225_0]
                              · linarith only [h0, h3212, h3220, h3222, h3224, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h3212, h3218, h3219, h3222, h3223, h5, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3210, h3220, h3222, h4, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h3208, h3210, h3211, h3212, h3213, h3219, hc23, hc34, hlam, hphi]
                    · linarith only [h3208, h3210, h3218, hc13, hc34, hlam, hphi]
                · linarith only [h3207, h3212, h3215, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h3212, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h3210, h3211, h4, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3267 | h3267
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3268 | h3268
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3269 | h3269
              · linarith only [h0, h3269, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3271 | h3271
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3272 | h3272
                  · linarith only [h1, h3208, h3272, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3274 | h3274
                    · linarith only [h1, h3210, h3274, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3276 | h3276
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3277 | h3277
                        · linarith only [h3208, h3277, h4, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3279 | h3279
                          · linarith only [h0, h3210, h3268, h3279, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3281 | h3281
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3282 | h3282
                              · rcases h0bigk with h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c | h3283c
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [hlam, p3283_0]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h0, h3271, h3279, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  rcases p3283_3 (m.d 0 1) (by simp) with h3286 | h3286
                                  · rcases p3283_3 (m.d 0 2) (by simp) with h3287 | h3287
                                    · linarith only [h0, h3287, hlam]
                                    · linarith only [h3287, h4, hlam]
                                  · linarith only [h1, h3286, hlam]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h0, h3271, h3279, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  rcases p3283_3 (m.d 0 1) (by simp) with h3292 | h3292
                                  · rcases p3283_3 (m.d 0 2) (by simp) with h3293 | h3293
                                    · linarith only [h0, h3293, hlam]
                                    · linarith only [h3207, h3293, hlam]
                                  · linarith only [h3, h3292, hlam]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h0, hlam, p3283_0]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [hlam, p3283_0]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h1, h3268, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h5, hlam, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h3277, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h1, hlam, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h4, hlam, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [hlam, p3283_0]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h3208, hlam, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h3210, hlam, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h2, hlam, p3283_0]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h0, h3271, h3279, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h1, h3268, h3277, h5, hc23, hc34, hlam, hphi, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [hlam, p3283_0]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h3, h3268, h3274, h3277, h5, hc23, hc34, hlam, hphi, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h3, hlam, p3283_0]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h3207, hlam, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h1, h3207, h3268, h3277, h5, hc23, hc34, hlam, hphi, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [h3267, hlam, p3283_1]
                                · have p3283_0 := h3283c.1
                                  have p3283_1 := h3283c.2.1
                                  have p3283_2 := h3283c.2.2.1
                                  have p3283_3 := h3283c.2.2.2
                                  linarith only [hlam, p3283_0]
                              · linarith only [h0, h3271, h3277, h3281, h3282, h5, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h3271, h3276, h3279, h3281, h5, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3208, h3267, h3268, h3269, h3276, hc23, hc34, hlam, hphi]
                · linarith only [h3207, h3268, h3271, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h3268, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h3207, h3267, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3323 | h3323
      · linarith only [h3323, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3325 | h3325
        · linarith only [h3207, h3325, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3327 | h3327
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3328 | h3328
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3329 | h3329
              · linarith only [h0, h3329, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3331 | h3331
                · linarith only [h0, h3207, h3331, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3333 | h3333
                  · linarith only [h1, h2, h3323, h3325, h3328, h3329, h3333, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3335 | h3335
                    · linarith only [h1, h3325, h3335, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3337 | h3337
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3338 | h3338
                        · linarith only [h3207, h3323, h3327, h3338, h4, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3340 | h3340
                          · linarith only [h3207, h3325, h3340, h4, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3342 | h3342
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3343 | h3343
                              · rcases h0bigk with h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c | h3344c
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h0, h3328, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  rcases p3344_3 (m.d 0 1) (by simp) with h3347 | h3347
                                  · rcases p3344_3 (m.d 0 2) (by simp) with h3348 | h3348
                                    · linarith only [h0, h3348, hlam]
                                    · linarith only [h3348, h4, hlam]
                                  · linarith only [h1, h3347, hlam]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h0, h3328, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h0, h3207, h3328, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h0, hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h1, h3207, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h5, hlam, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h3207, hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h1, hlam, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h4, hlam, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h3323, hlam, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h3325, hlam, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h2, hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h0, h3328, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h1, h3338, h5, hc13, hc34, hlam, hphi, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h0, h3207, h3328, h3338, h5, hc23, hc34, hlam, hphi, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h3, hlam, p3344_0]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h0, h3328, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h1, h3207, h3340, hc13, hc35, hlam, hphi, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [h3327, hlam, p3344_1]
                                · have p3344_0 := h3344c.1
                                  have p3344_1 := h3344c.2.1
                                  have p3344_2 := h3344c.2.2.1
                                  have p3344_3 := h3344c.2.2.2
                                  linarith only [hlam, p3344_0]
                              · linarith only [h2, h3337, h3338, h3343, h5, hlam]
                            · linarith only [h2, h3337, h3342, h5, hlam]
                      · linarith only [h3323, h3327, h3328, h3329, h3337, hc23, hc34, hlam, hphi]
            · linarith only [h3328, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3378 | h3378
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3379 | h3379
              · linarith only [h0, h3379, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3381 | h3381
                · linarith only [h0, h3207, h3381, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3383 | h3383
                  · linarith only [h1, h3323, h3383, h4, h5, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3385 | h3385
                    · linarith only [h1, h3325, h3385, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3387 | h3387
                      · linarith only [h2, h3327, h3387, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3389 | h3389
                        · linarith only [h0, h3323, h3378, h3389, h5, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3391 | h3391
                          · linarith only [h0, h3325, h3327, h3378, h3391, h5, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3393 | h3393
                            · linarith only [h0, h3327, h3378, h3389, h3393, h5, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h3378, h3393, h5, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h3378, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s4 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3397 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h3398 | h3398
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3399 | h3399
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3400 | h3400
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3401 | h3401
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3402 | h3402
          · linarith only [h0, h3397, h3402, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3404 | h3404
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3405 | h3405
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3406 | h3406
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3407 | h3407
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3408 | h3408
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3409 | h3409
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3410 | h3410
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3411 | h3411
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3412 | h3412
                            · rcases h0bigk with h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c | h3413c
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h0, h3404, h3409, h3412, hc01, hc45, hlam, hphi, ht0b, ht5b, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h0, h3404, h3409, h3412, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3397, h3409, h3412, hc01, hc45, hlam, hphi, ht0b, ht5b, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                rcases p3413_3 (m.d 0 1) (by simp) with h3418 | h3418
                                · rcases p3413_3 (m.d 0 2) (by simp) with h3419 | h3419
                                  · linarith only [h0, h3419, hlam]
                                  · linarith only [h3398, h3419, hlam]
                                · linarith only [h3, h3418, hlam]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h0, hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h4, hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h2, h3404, h3409, h3412, hc02, hc45, hlam, hphi, ht0b, ht5b, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h1, hlam, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h4, hc02, hc23, hlam, hphi, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h2, h3404, h3409, h3412, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                rcases p3413_3 (m.d 0 1) (by simp) with h3432 | h3432
                                · rcases p3413_3 (m.d 0 2) (by simp) with h3433 | h3433
                                  · linarith only [h3433, h4, hlam]
                                  · linarith only [h3398, h3433, hlam]
                                · linarith only [h3, h3432, hlam]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h2, hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3397, hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3399, hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3, h3397, h3405, h3410, h3412, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3, hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3398, hlam, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3400, hlam, p3413_0]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [h3401, hlam, p3413_1]
                              · have p3413_0 := h3413c.1
                                have p3413_1 := h3413c.2.1
                                have p3413_2 := h3413c.2.2.1
                                have p3413_3 := h3413c.2.2.2
                                linarith only [hlam, p3413_0]
                            · linarith only [h0, h3404, h3411, h3412, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3448 | h3448
                            · linarith only [h3409, h3411, h3448, hlam]
                            · rcases h0bigk with h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c | h3450c
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h2, h3397, h3408, h3409, h3411, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h2, h3397, h3408, h3409, h3411, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h2, h3408, h3409, h3411, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3, h3408, h3409, h3411, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h0, hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h4, hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h2, h3408, h3409, h3411, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3, h3408, h3409, h3411, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h1, hlam, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h0, h4, hc12, hc23, hlam, hphi, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h2, h3408, h3409, h3411, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3, h3408, h3409, h3411, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h2, hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3397, hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3399, hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3, h3397, h3408, h3409, h3411, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3, hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3398, hlam, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3400, hlam, p3450_0]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [h3401, hlam, p3450_1]
                              · have p3450_0 := h3450c.1
                                have p3450_1 := h3450c.2.1
                                have p3450_2 := h3450c.2.2.1
                                have p3450_3 := h3450c.2.2.2
                                linarith only [hlam, p3450_0]
                        · linarith only [h3400, h3410, h4, hlam]
                      · linarith only [h3399, h3409, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3478 | h3478
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3479 | h3479
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3480 | h3480
                          · linarith only [h3404, h3408, h3480, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3482 | h3482
                            · linarith only [h3404, h3408, h3478, h3482, hlam]
                            · rcases h0bigk with h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c | h3484c
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3397, h3401, h3404, h3408, h3478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3397, h3401, h3404, h3408, h3478, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3401, h3404, h3408, h3478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3401, h3404, h3408, h3478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h0, hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h4, hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3401, h3404, h3408, h3478, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3401, h3404, h3408, h3478, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h1, hlam, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h0, h3405, hc03, hc25, hlam, hphi, ht0b, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3401, h3404, h3408, h3478, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3401, h3404, h3408, h3478, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h2, hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3397, hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3399, hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3397, h3401, h3404, h3408, h3478, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3, hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3398, hlam, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3400, hlam, p3484_0]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [h3401, hlam, p3484_1]
                              · have p3484_0 := h3484c.1
                                have p3484_1 := h3484c.2.1
                                have p3484_2 := h3484c.2.2.1
                                have p3484_3 := h3484c.2.2.2
                                linarith only [hlam, p3484_0]
                        · linarith only [h3400, h3479, h4, hlam]
                      · linarith only [h3399, h3478, h4, hlam]
                  · linarith only [h3402, h3405, h3407, hlam]
                · linarith only [h3402, h3404, h3406, hlam]
              · linarith only [h3398, h3405, h4, hc12, hc23, hlam, hphi]
            · linarith only [h3397, h3404, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3516 | h3516
          · linarith only [h0, h3397, h3516, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3518 | h3518
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3519 | h3519
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3520 | h3520
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3521 | h3521
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3522 | h3522
                    · linarith only [h2, h3401, h3522, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3524 | h3524
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3525 | h3525
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3526 | h3526
                          · linarith only [h2, h3401, h3518, h3526, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3528 | h3528
                            · linarith only [h2, h3401, h3518, h3524, h3528, hlam]
                            · rcases h0bigk with h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h0, h3519, hc01, hc25, hlam, hphi, ht0b, ht5b, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h0, h3519, h3525, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                rcases p3530_3 (m.d 0 1) (by simp) with h3534 | h3534
                                · rcases p3530_3 (m.d 0 2) (by simp) with h3535 | h3535
                                  · linarith only [h0, h3535, hlam]
                                  · linarith only [h3397, h3535, hlam]
                                · linarith only [h2, h3534, hlam]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                rcases p3530_3 (m.d 0 1) (by simp) with h3539 | h3539
                                · rcases p3530_3 (m.d 0 2) (by simp) with h3540 | h3540
                                  · linarith only [h0, h3540, hlam]
                                  · linarith only [h3398, h3540, hlam]
                                · linarith only [h3, h3539, hlam]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h0, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h4, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h2, h3518, h3524, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h2, h3401, h3518, h3524, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h1, hlam, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h0, h3519, h3524, h3526, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                rcases p3530_3 (m.d 0 1) (by simp) with h3552 | h3552
                                · rcases p3530_3 (m.d 0 2) (by simp) with h3553 | h3553
                                  · linarith only [h3553, h4, hlam]
                                  · linarith only [h3397, h3553, hlam]
                                · linarith only [h2, h3552, hlam]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                rcases p3530_3 (m.d 0 1) (by simp) with h3557 | h3557
                                · rcases p3530_3 (m.d 0 2) (by simp) with h3558 | h3558
                                  · linarith only [h3558, h4, hlam]
                                  · linarith only [h3398, h3558, hlam]
                                · linarith only [h3, h3557, hlam]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h2, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h3397, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h3399, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h3401, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h3, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h3398, hlam, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h3400, hlam, p3530_0]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [h2, h3398, h3518, h3524, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3530_1]
                              · have p3530_0 := h3530c.1
                                have p3530_1 := h3530c.2.1
                                have p3530_2 := h3530c.2.2.1
                                have p3530_3 := h3530c.2.2.2
                                linarith only [hlam, p3530_0]
                        · linarith only [h3400, h3525, h4, hlam]
                      · linarith only [h3399, h3524, h4, hlam]
                  · linarith only [h3516, h3519, h3521, hlam]
                · linarith only [h3399, h3401, h3516, h3518, h3520, hc24, hc45, hlam, hphi]
              · linarith only [h3398, h3518, h3519, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h3397, h3518, h4, hc12, hc23, hlam, hphi]
      · linarith only [h3398, h3400, h4, hlam]
    · linarith only [h3397, h3399, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3580 | h3580
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3581 | h3581
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3582 | h3582
        · linarith only [h3397, h3398, h3582, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3584 | h3584
          · linarith only [h0, h3584, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3586 | h3586
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3587 | h3587
              · linarith only [h0, h3398, h3587, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3589 | h3589
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3590 | h3590
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3591 | h3591
                    · linarith only [h2, h3582, h3591, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3593 | h3593
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3594 | h3594
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3595 | h3595
                          · linarith only [h0, h2, h3398, h3582, h3586, h3594, h3595, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3597 | h3597
                            · linarith only [h0, h3398, h3586, h3593, h3595, h3597, hlam]
                            · rcases h0bigk with h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c | h3599c
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h0, h3586, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h0, h3398, h3581, h3586, h3593, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                rcases p3599_3 (m.d 0 1) (by simp) with h3603 | h3603
                                · rcases p3599_3 (m.d 0 2) (by simp) with h3604 | h3604
                                  · linarith only [h0, h3604, hlam]
                                  · linarith only [h3397, h3604, hlam]
                                · linarith only [h2, h3603, hlam]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h0, h3398, h3586, h3593, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h0, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h4, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h2, h3398, h3586, h3593, h3594, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h3398, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h1, hlam, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h0, h3586, h3593, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                rcases p3599_3 (m.d 0 1) (by simp) with h3617 | h3617
                                · rcases p3599_3 (m.d 0 2) (by simp) with h3618 | h3618
                                  · linarith only [h3618, h4, hlam]
                                  · linarith only [h3397, h3618, hlam]
                                · linarith only [h2, h3617, hlam]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h0, h3398, h3586, h3593, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h2, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h3397, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h3580, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h3582, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h3, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h0, h3586, h3593, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h3581, hlam, p3599_0]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [h2, h3398, h3586, h3593, h3595, hc34, hc45, hlam, hphi, p3599_1]
                              · have p3599_0 := h3599c.1
                                have p3599_1 := h3599c.2.1
                                have p3599_2 := h3599c.2.2.1
                                have p3599_3 := h3599c.2.2.2
                                linarith only [hlam, p3599_0]
                        · linarith only [h1, h3590, h3594, h4, hlam]
                      · linarith only [h3580, h3593, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3635 | h3635
                    · linarith only [h2, h3397, h3398, h3582, h3635, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3637 | h3637
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3638 | h3638
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3639 | h3639
                          · linarith only [h3581, h3582, h3584, h3586, h3590, h3639, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3641 | h3641
                            · linarith only [h3397, h3398, h3637, h3639, h3641, hlam]
                            · rcases h0bigk with h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c | h3643c
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h0, h3586, h3637, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3581, h3584, h3586, h3590, h3637, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                rcases p3643_3 (m.d 0 1) (by simp) with h3647 | h3647
                                · rcases p3643_3 (m.d 0 2) (by simp) with h3648 | h3648
                                  · linarith only [h0, h3648, hlam]
                                  · linarith only [h3397, h3648, hlam]
                                · linarith only [h2, h3647, hlam]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3581, h3584, h3586, h3590, h3637, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h0, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h4, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h2, h3586, h3637, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3398, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h1, hlam, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h0, h3586, h3637, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                rcases p3643_3 (m.d 0 1) (by simp) with h3661 | h3661
                                · rcases p3643_3 (m.d 0 2) (by simp) with h3662 | h3662
                                  · linarith only [h3662, h4, hlam]
                                  · linarith only [h3397, h3662, hlam]
                                · linarith only [h2, h3661, hlam]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3581, h3584, h3586, h3590, h3637, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h2, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3397, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3580, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3582, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h0, h3586, h3637, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h3581, hlam, p3643_0]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [h2, h3398, h3586, h3637, h3639, hc34, hc45, hlam, hphi, p3643_1]
                              · have p3643_0 := h3643c.1
                                have p3643_1 := h3643c.2.1
                                have p3643_2 := h3643c.2.2.1
                                have p3643_3 := h3643c.2.2.2
                                linarith only [hlam, p3643_0]
                        · linarith only [h3581, h3638, h4, hlam]
                      · linarith only [h3581, h3584, h3586, h3590, h3637, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h3580, h3582, h3584, h3586, h3589, hc24, hc45, hlam, hphi]
            · linarith only [h3397, h3398, h3586, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3681 | h3681
        · linarith only [h3397, h3398, h3681, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3683 | h3683
          · linarith only [h0, h3397, h3683, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3685 | h3685
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3686 | h3686
              · linarith only [h0, h3398, h3686, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3688 | h3688
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3689 | h3689
                  · linarith only [h1, h3581, h3689, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3691 | h3691
                    · linarith only [h2, h3681, h3691, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3693 | h3693
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3694 | h3694
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3695 | h3695
                          · linarith only [h0, h3581, h3685, h3694, h3695, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3697 | h3697
                            · linarith only [h0, h3581, h3685, h3693, h3694, h3695, h3697, h4, hlam]
                            · rcases h0bigk with h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c | h3699c
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h0, h3685, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h0, h3685, h3693, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                rcases p3699_3 (m.d 0 1) (by simp) with h3703 | h3703
                                · rcases p3699_3 (m.d 0 2) (by simp) with h3704 | h3704
                                  · linarith only [h0, h3704, hlam]
                                  · linarith only [h3397, h3704, hlam]
                                · linarith only [h2, h3703, hlam]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3, h3683, h3685, h3689, h3693, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h0, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h4, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3581, h3694, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3398, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h1, hlam, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3581, h3694, hc02, hc23, hlam, hphi, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3397, h3581, h3693, h3694, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3581, hlam, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h2, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3397, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3580, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3681, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3, hlam, p3699_0]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h0, h3685, h3693, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3581, h3694, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [h3397, h3581, h3693, h3694, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3699_1]
                              · have p3699_0 := h3699c.1
                                have p3699_1 := h3699c.2.1
                                have p3699_2 := h3699c.2.2.1
                                have p3699_3 := h3699c.2.2.2
                                linarith only [hlam, p3699_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3729 | h3729
                          · linarith only [h0, h3681, h3685, h3694, h3729, h4, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3731 | h3731
                            · linarith only [h0, h3685, h3693, h3694, h3729, h3731, h4, hlam]
                            · linarith only [h0, h3685, h3693, h3694, h3731, h4, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h3580, h3685, h3693, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h3580, h3581, h3683, h3685, h3688, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h3397, h3685, h4, hc12, hc23, hlam, hphi]
    · linarith only [h3397, h3580, h4, hlam]

end R2N4
