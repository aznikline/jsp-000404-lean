import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x0 (m : N7Model)
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
    (h3239 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h3240 | h3240
  · rcases h2bigk with h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c | h3241c
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h0, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3237, h3240, hc02, hc45, hlam, hphi, ht0b, ht5b, p3241_1]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      rcases p3241_3 (m.d 0 2) (by simp) with h3245 | h3245
      · rcases p3241_3 (m.d 1 2) (by simp) with h3246 | h3246
        · rcases p3241_3 (m.d 2 3) (by simp) with h3247 | h3247
          · linarith only [h3225, h3247, hlam]
          · linarith only [h3237, h3247, hlam]
        · linarith only [h3232, h3246, hlam]
      · linarith only [h3245, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      rcases p3241_3 (m.d 0 2) (by simp) with h3252 | h3252
      · rcases p3241_3 (m.d 1 2) (by simp) with h3253 | h3253
        · rcases p3241_3 (m.d 2 3) (by simp) with h3254 | h3254
          · linarith only [h3225, h3254, hlam]
          · linarith only [h3238, h3254, hlam]
        · linarith only [h3233, h3253, hlam]
      · linarith only [h3252, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h0, hc12, hlam, hphi, p3241_1, u1ehi0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3237, h3240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3241_1]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      rcases p3241_3 (m.d 0 2) (by simp) with h3262 | h3262
      · linarith only [h0, h3262, hlam]
      · linarith only [h3226, h3262, hlam]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      rcases p3241_3 (m.d 0 2) (by simp) with h3265 | h3265
      · linarith only [h0, h3265, hlam]
      · linarith only [h3227, h3265, hlam]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3225, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3231, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3225, h3237, h3240, hc02, hc45, hlam, hphi, ht0b, ht5b, p3241_1]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      rcases p3241_3 (m.d 0 2) (by simp) with h3272 | h3272
      · rcases p3241_3 (m.d 1 2) (by simp) with h3273 | h3273
        · rcases p3241_3 (m.d 2 3) (by simp) with h3274 | h3274
          · rcases p3241_3 (m.d 2 4) (by simp) with h3275 | h3275
            · linarith only [h3237, h3275, hlam]
            · linarith only [h3239, h3275, hlam]
          · linarith only [h3238, h3274, hlam]
        · linarith only [h3233, h3273, hlam]
      · linarith only [h3227, h3272, hlam]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3226, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3232, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3237, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      rcases p3241_3 (m.d 0 2) (by simp) with h3285 | h3285
      · rcases p3241_3 (m.d 1 2) (by simp) with h3286 | h3286
        · rcases p3241_3 (m.d 2 3) (by simp) with h3287 | h3287
          · rcases p3241_3 (m.d 2 4) (by simp) with h3288 | h3288
            · rcases p3241_3 (m.d 2 5) (by simp) with h3289 | h3289
              · linarith only [h3239, h3289, hlam]
              · rcases h2emax with h3291 | h3291 | h3291 | h3291 | h3291
                · linarith only [h0, h3291, hlam, ht12, u1ehi0]
                · linarith only [h3291, hlam, ht12, u1ehi1]
                · linarith only [h3237, h3238, h3240, h3291, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3241_1]
                · linarith only [h3238, h3240, h3291, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3241_1]
                · rcases h4bigk with h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c | h3296c
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3221, hlam, p3296_1]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3228, h3238, h3240, hc03, hc45, hlam, hphi, ht0b, ht5b, p3241_1, p3296_1]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    rcases p3296_3 (m.d 0 4) (by simp) with h3300 | h3300
                    · rcases p3296_3 (m.d 1 4) (by simp) with h3301 | h3301
                      · rcases p3296_3 (m.d 2 4) (by simp) with h3302 | h3302
                        · linarith only [h3226, h3302, hlam]
                        · linarith only [h3237, h3302, hlam]
                      · linarith only [h3234, h3301, hlam]
                    · linarith only [h3228, h3300, hlam]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    rcases p3296_3 (m.d 0 4) (by simp) with h3307 | h3307
                    · rcases p3296_3 (m.d 1 4) (by simp) with h3308 | h3308
                      · rcases p3296_3 (m.d 2 4) (by simp) with h3309 | h3309
                        · linarith only [h3226, h3309, hlam]
                        · linarith only [h3239, h3309, hlam]
                      · linarith only [h3236, h3308, hlam]
                    · linarith only [h3307, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3221, hc14, hlam, hphi, p3296_1, u1ehi0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3232, h3238, h3240, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3241_1, p3296_1]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    rcases p3296_3 (m.d 0 4) (by simp) with h3317 | h3317
                    · linarith only [h3221, h3317, hlam]
                    · linarith only [h3228, h3317, hlam]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    rcases p3296_3 (m.d 0 4) (by simp) with h3320 | h3320
                    · linarith only [h3221, h3320, hlam]
                    · linarith only [h3230, h3320, hlam]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3226, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3232, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3225, h3237, h3240, hc02, hc45, hlam, hphi, ht0b, ht5b, p3296_1]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    rcases p3296_3 (m.d 0 4) (by simp) with h3327 | h3327
                    · rcases p3296_3 (m.d 1 4) (by simp) with h3328 | h3328
                      · rcases p3296_3 (m.d 2 4) (by simp) with h3329 | h3329
                        · rcases p3296_3 (m.d 3 4) (by simp) with h3330 | h3330
                          · linarith only [h3237, h3330, hlam]
                          · linarith only [h3240, h3330, hlam]
                        · linarith only [h3329, hlam, p3296_0]
                      · linarith only [h3236, h3328, hlam]
                    · linarith only [h3230, h3327, hlam]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3228, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3234, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3237, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h0, h3225, h3237, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3296_1]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3230, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3236, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3239, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [h3240, hlam, p3296_0]
                  · have p3296_0 := h3296c.1
                    have p3296_1 := h3296c.2.1
                    have p3296_2 := h3296c.2.2.1
                    have p3296_3 := h3296c.2.2.2
                    linarith only [hlam, p3296_0]
            · linarith only [h3239, h3288, hlam]
          · linarith only [h3238, h3287, hlam]
        · linarith only [h3233, h3286, hlam]
      · linarith only [h3227, h3285, hlam]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3227, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3233, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3238, hlam, p3241_0]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [h3239, hlam, p3241_1]
    · have p3241_0 := h3241c.1
      have p3241_1 := h3241c.2.1
      have p3241_2 := h3241c.2.2.1
      have p3241_3 := h3241c.2.2.2
      linarith only [hlam, p3241_0]
  · rcases h2bigk with h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c | h3355c
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h0, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h0, h3237, h3239, h3240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h0, h3239, h3240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      rcases p3355_3 (m.d 0 2) (by simp) with h3360 | h3360
      · rcases p3355_3 (m.d 1 2) (by simp) with h3361 | h3361
        · rcases p3355_3 (m.d 2 3) (by simp) with h3362 | h3362
          · linarith only [h3225, h3362, hlam]
          · linarith only [h3238, h3362, hlam]
        · linarith only [h3233, h3361, hlam]
      · linarith only [h3360, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h0, hc12, hlam, hphi, p3355_1, u1ehi0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3237, h3239, h3240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3239, h3240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      rcases p3355_3 (m.d 0 2) (by simp) with h3371 | h3371
      · linarith only [h0, h3371, hlam]
      · linarith only [h3227, h3371, hlam]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3225, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3231, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3225, h3239, h3240, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h0, h3225, h3239, h3240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3226, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3232, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3237, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h0, h3226, h3239, h3240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3227, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3233, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3238, hlam, p3355_0]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [h3239, hlam, p3355_1]
    · have p3355_0 := h3355c.1
      have p3355_1 := h3355c.2.1
      have p3355_2 := h3355c.2.2.1
      have p3355_3 := h3355c.2.2.2
      linarith only [hlam, p3355_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x0 (m : N7Model)
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
    (h3389 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  linarith only [h0, h3225, h3237, h3239, h3389, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x0 (m : N7Model)
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
    (h3391c : ((m.d 0 2) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 2) ∧ (m.d 0 2) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 0 2) ∨ (m.d 0 2) ≤ z)))
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
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x1 (m : N7Model)
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
    (h3391c : ((m.d 0 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 2) ∧ (m.d 1 2) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 0 2) ∨ (m.d 1 2) ≤ z)))
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
  linarith only [h0, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x2 (m : N7Model)
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
    (h3391c : ((m.d 0 2) < (m.d 2 3) ∧ 2 * m.lam ≤ (m.d 2 3) - (m.d 0 2) ∧ (m.d 2 3) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 0 2) ∨ (m.d 2 3) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3394 | h3394
  · rcases p3391_3 (m.d 1 2) (by simp) with h3395 | h3395
    · rcases p3391_3 (m.d 2 3) (by simp) with h3396 | h3396
      · linarith only [h3396, hlam, p3391_0]
      · rcases p3391_3 (m.d 2 4) (by simp) with h3398 | h3398
        · linarith only [h3226, h3398, hlam]
        · rcases p3391_3 (m.d 2 5) (by simp) with h3400 | h3400
          · linarith only [h3227, h3400, hlam]
          · rcases h2emax with h3402 | h3402 | h3402 | h3402 | h3402
            · linarith only [h3402, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3391_1]
            · linarith only [h3402, hlam, ht12, u1ehi1]
            · rcases h4bigk with h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c | h3405c
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3221, hlam, p3405_1]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3408 | h3408
                · rcases p3405_3 (m.d 1 4) (by simp) with h3409 | h3409
                  · rcases p3405_3 (m.d 2 4) (by simp) with h3410 | h3410
                    · linarith only [h3226, h3410, hlam]
                    · rcases p3405_3 (m.d 3 4) (by simp) with h3412 | h3412
                      · linarith only [h3228, h3412, hlam]
                      · rcases p3405_3 (m.d 4 5) (by simp) with h3414 | h3414
                        · linarith only [h3230, h3414, hlam]
                        · linarith only [h3239, h3414, hlam]
                  · linarith only [h3232, h3409, hlam]
                · linarith only [h3226, h3408, hlam]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3419 | h3419
                · rcases p3405_3 (m.d 1 4) (by simp) with h3420 | h3420
                  · rcases p3405_3 (m.d 2 4) (by simp) with h3421 | h3421
                    · linarith only [h3226, h3421, hlam]
                    · linarith only [h3237, h3421, hlam]
                  · linarith only [h3234, h3420, hlam]
                · linarith only [h3228, h3419, hlam]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3426 | h3426
                · rcases p3405_3 (m.d 1 4) (by simp) with h3427 | h3427
                  · rcases p3405_3 (m.d 2 4) (by simp) with h3428 | h3428
                    · linarith only [h3226, h3428, hlam]
                    · rcases p3405_3 (m.d 3 4) (by simp) with h3430 | h3430
                      · linarith only [h3228, h3430, hlam]
                      · rcases p3405_3 (m.d 4 5) (by simp) with h3432 | h3432
                        · linarith only [h3432, hlam, p3405_0]
                        · rcases h5bigk with h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c | h3434c
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [hlam, p3434_0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3223, hlam, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            rcases p3434_3 (m.d 0 5) (by simp) with h3437 | h3437
                            · rcases p3434_3 (m.d 1 5) (by simp) with h3438 | h3438
                              · rcases p3434_3 (m.d 2 5) (by simp) with h3439 | h3439
                                · linarith only [h3227, h3439, hlam]
                                · rcases p3434_3 (m.d 3 5) (by simp) with h3441 | h3441
                                  · linarith only [h3229, h3441, hlam]
                                  · rcases p3434_3 (m.d 4 5) (by simp) with h3443 | h3443
                                    · linarith only [h3230, h3443, hlam]
                                    · linarith only [h3239, h3443, hlam]
                              · linarith only [h3233, h3438, hlam]
                            · linarith only [h3227, h3437, hlam]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            rcases p3434_3 (m.d 0 5) (by simp) with h3448 | h3448
                            · rcases p3434_3 (m.d 1 5) (by simp) with h3449 | h3449
                              · rcases p3434_3 (m.d 2 5) (by simp) with h3450 | h3450
                                · linarith only [h3227, h3450, hlam]
                                · linarith only [h3238, h3450, hlam]
                              · linarith only [h3235, h3449, hlam]
                            · linarith only [h3229, h3448, hlam]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3225, h3228, h3230, h3237, h3239, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3223, hc15, hlam, hphi, p3434_1, u1ehi0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [hlam, p3434_0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            rcases p3434_3 (m.d 0 5) (by simp) with h3458 | h3458
                            · linarith only [h3223, h3458, hlam]
                            · linarith only [h3227, h3458, hlam]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            rcases p3434_3 (m.d 0 5) (by simp) with h3461 | h3461
                            · linarith only [h3223, h3461, hlam]
                            · linarith only [h3229, h3461, hlam]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, h3239, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3227, hlam, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3233, hlam, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [hlam, p3434_0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3239, hlam, p3434_0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3229, hlam, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3235, hlam, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3238, hlam, p3434_0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [hlam, p3434_0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3389, hlam, p3434_0]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3230, hlam, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h3236, hlam, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h0, h3225, h3228, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3405_1, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [h0, h3225, h3228, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3405_1, p3434_1]
                          · have p3434_0 := h3434c.1
                            have p3434_1 := h3434c.2.1
                            have p3434_2 := h3434c.2.2.1
                            have p3434_3 := h3434c.2.2.2
                            linarith only [hlam, p3434_0]
                  · linarith only [h3236, h3427, hlam]
                · linarith only [h3426, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p3405_1, u1ehi0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3484 | h3484
                · linarith only [h3221, h3484, hlam]
                · linarith only [h3226, h3484, hlam]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3487 | h3487
                · linarith only [h3221, h3487, hlam]
                · linarith only [h3228, h3487, hlam]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3490 | h3490
                · linarith only [h3221, h3490, hlam]
                · linarith only [h3230, h3490, hlam]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3226, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3232, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3230, h3239, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3405_1]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3239, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3228, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3234, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3237, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3389, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3230, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [h3236, hlam, p3405_0]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3505 | h3505
                · rcases p3405_3 (m.d 1 4) (by simp) with h3506 | h3506
                  · rcases p3405_3 (m.d 2 4) (by simp) with h3507 | h3507
                    · linarith only [h3507, hlam, p3405_0]
                    · rcases p3405_3 (m.d 3 4) (by simp) with h3509 | h3509
                      · linarith only [h3389, h3509, hlam]
                      · rcases p3405_3 (m.d 4 5) (by simp) with h3511 | h3511
                        · rcases h5bigk with h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c | h3512c
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [hlam, p3512_0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3223, hlam, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            rcases p3512_3 (m.d 0 5) (by simp) with h3515 | h3515
                            · rcases p3512_3 (m.d 1 5) (by simp) with h3516 | h3516
                              · rcases p3512_3 (m.d 2 5) (by simp) with h3517 | h3517
                                · linarith only [h3227, h3517, hlam]
                                · rcases p3512_3 (m.d 3 5) (by simp) with h3519 | h3519
                                  · linarith only [h3229, h3519, hlam]
                                  · rcases p3512_3 (m.d 4 5) (by simp) with h3521 | h3521
                                    · linarith only [h3230, h3521, hlam]
                                    · linarith only [h3239, h3521, hlam]
                              · linarith only [h3233, h3516, hlam]
                            · linarith only [h3227, h3515, hlam]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            rcases p3512_3 (m.d 0 5) (by simp) with h3526 | h3526
                            · rcases p3512_3 (m.d 1 5) (by simp) with h3527 | h3527
                              · rcases p3512_3 (m.d 2 5) (by simp) with h3528 | h3528
                                · linarith only [h3227, h3528, hlam]
                                · linarith only [h3238, h3528, hlam]
                              · linarith only [h3235, h3527, hlam]
                            · linarith only [h3229, h3526, hlam]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3405_1, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p3512_1, u1ehi0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [hlam, p3512_0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            rcases p3512_3 (m.d 0 5) (by simp) with h3536 | h3536
                            · linarith only [h3223, h3536, hlam]
                            · linarith only [h3227, h3536, hlam]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            rcases p3512_3 (m.d 0 5) (by simp) with h3539 | h3539
                            · linarith only [h3223, h3539, hlam]
                            · linarith only [h3229, h3539, hlam]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3405_1, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3227, hlam, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3233, hlam, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [hlam, p3512_0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3239, hlam, p3512_0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3229, hlam, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3235, hlam, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3238, hlam, p3512_0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [hlam, p3512_0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3389, hlam, p3512_0]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3230, hlam, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3236, hlam, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3221, h3230, h3231, h3234, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [h3221, h3230, h3231, h3234, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3512_1]
                          · have p3512_0 := h3512c.1
                            have p3512_1 := h3512c.2.1
                            have p3512_2 := h3512c.2.2.1
                            have p3512_3 := h3512c.2.2.2
                            linarith only [hlam, p3512_0]
                        · linarith only [h3511, hlam, p3405_0]
                  · linarith only [h3232, h3506, hlam]
                · linarith only [h3226, h3505, hlam]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                rcases p3405_3 (m.d 0 4) (by simp) with h3561 | h3561
                · rcases p3405_3 (m.d 1 4) (by simp) with h3562 | h3562
                  · rcases p3405_3 (m.d 2 4) (by simp) with h3563 | h3563
                    · linarith only [h3239, h3563, hlam]
                    · linarith only [h3237, h3563, hlam]
                  · linarith only [h3234, h3562, hlam]
                · linarith only [h3228, h3561, hlam]
              · have p3405_0 := h3405c.1
                have p3405_1 := h3405c.2.1
                have p3405_2 := h3405c.2.2.1
                have p3405_3 := h3405c.2.2.2
                linarith only [hlam, p3405_0]
            · rcases h4bigk with h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c | h3569c
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3221, hlam, p3569_1]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3572 | h3572
                · rcases p3569_3 (m.d 1 4) (by simp) with h3573 | h3573
                  · rcases p3569_3 (m.d 2 4) (by simp) with h3574 | h3574
                    · linarith only [h3226, h3574, hlam]
                    · rcases p3569_3 (m.d 3 4) (by simp) with h3576 | h3576
                      · linarith only [h3228, h3576, hlam]
                      · rcases p3569_3 (m.d 4 5) (by simp) with h3578 | h3578
                        · linarith only [h3230, h3578, hlam]
                        · linarith only [h3239, h3578, hlam]
                  · linarith only [h3232, h3573, hlam]
                · linarith only [h3226, h3572, hlam]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3583 | h3583
                · rcases p3569_3 (m.d 1 4) (by simp) with h3584 | h3584
                  · rcases p3569_3 (m.d 2 4) (by simp) with h3585 | h3585
                    · linarith only [h3226, h3585, hlam]
                    · linarith only [h3237, h3585, hlam]
                  · linarith only [h3234, h3584, hlam]
                · linarith only [h3228, h3583, hlam]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3590 | h3590
                · rcases p3569_3 (m.d 1 4) (by simp) with h3591 | h3591
                  · rcases p3569_3 (m.d 2 4) (by simp) with h3592 | h3592
                    · linarith only [h3226, h3592, hlam]
                    · rcases p3569_3 (m.d 3 4) (by simp) with h3594 | h3594
                      · linarith only [h3228, h3594, hlam]
                      · rcases p3569_3 (m.d 4 5) (by simp) with h3596 | h3596
                        · linarith only [h3596, hlam, p3569_0]
                        · rcases h5bigk with h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c | h3598c
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [hlam, p3598_0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3223, hlam, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            rcases p3598_3 (m.d 0 5) (by simp) with h3601 | h3601
                            · rcases p3598_3 (m.d 1 5) (by simp) with h3602 | h3602
                              · rcases p3598_3 (m.d 2 5) (by simp) with h3603 | h3603
                                · linarith only [h3227, h3603, hlam]
                                · rcases p3598_3 (m.d 3 5) (by simp) with h3605 | h3605
                                  · linarith only [h3229, h3605, hlam]
                                  · rcases p3598_3 (m.d 4 5) (by simp) with h3607 | h3607
                                    · linarith only [h3230, h3607, hlam]
                                    · linarith only [h3239, h3607, hlam]
                              · linarith only [h3233, h3602, hlam]
                            · linarith only [h3227, h3601, hlam]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            rcases p3598_3 (m.d 0 5) (by simp) with h3612 | h3612
                            · rcases p3598_3 (m.d 1 5) (by simp) with h3613 | h3613
                              · rcases p3598_3 (m.d 2 5) (by simp) with h3614 | h3614
                                · linarith only [h3227, h3614, hlam]
                                · linarith only [h3238, h3614, hlam]
                              · linarith only [h3235, h3613, hlam]
                            · linarith only [h3229, h3612, hlam]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3230, hlam, p3569_2, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p3598_1, u1ehi0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [hlam, p3598_0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            rcases p3598_3 (m.d 0 5) (by simp) with h3622 | h3622
                            · linarith only [h3223, h3622, hlam]
                            · linarith only [h3227, h3622, hlam]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            rcases p3598_3 (m.d 0 5) (by simp) with h3625 | h3625
                            · linarith only [h3223, h3625, hlam]
                            · linarith only [h3229, h3625, hlam]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, h3239, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3227, hlam, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3233, hlam, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [hlam, p3598_0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3239, hlam, p3598_0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3229, hlam, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3235, hlam, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3238, hlam, p3598_0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [hlam, p3598_0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3389, hlam, p3598_0]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3230, hlam, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3236, hlam, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3221, h3231, h3234, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3569_1, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [h3221, h3231, h3234, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3569_1, p3598_1]
                          · have p3598_0 := h3598c.1
                            have p3598_1 := h3598c.2.1
                            have p3598_2 := h3598c.2.2.1
                            have p3598_3 := h3598c.2.2.2
                            linarith only [hlam, p3598_0]
                  · linarith only [h3236, h3591, hlam]
                · linarith only [h3590, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p3569_1, u1ehi0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3648 | h3648
                · linarith only [h3221, h3648, hlam]
                · linarith only [h3226, h3648, hlam]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3651 | h3651
                · linarith only [h3221, h3651, hlam]
                · linarith only [h3228, h3651, hlam]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3654 | h3654
                · linarith only [h3221, h3654, hlam]
                · linarith only [h3230, h3654, hlam]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3226, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3232, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3230, h3239, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3569_1]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3239, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3228, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3234, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3237, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3389, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3230, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [h3236, hlam, p3569_0]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3669 | h3669
                · rcases p3569_3 (m.d 1 4) (by simp) with h3670 | h3670
                  · rcases p3569_3 (m.d 2 4) (by simp) with h3671 | h3671
                    · linarith only [h3671, hlam, p3569_0]
                    · rcases p3569_3 (m.d 3 4) (by simp) with h3673 | h3673
                      · linarith only [h3389, h3673, hlam]
                      · rcases p3569_3 (m.d 4 5) (by simp) with h3675 | h3675
                        · rcases h5bigk with h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c | h3676c
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [hlam, p3676_0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3223, hlam, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            rcases p3676_3 (m.d 0 5) (by simp) with h3679 | h3679
                            · rcases p3676_3 (m.d 1 5) (by simp) with h3680 | h3680
                              · rcases p3676_3 (m.d 2 5) (by simp) with h3681 | h3681
                                · linarith only [h3227, h3681, hlam]
                                · rcases p3676_3 (m.d 3 5) (by simp) with h3683 | h3683
                                  · linarith only [h3229, h3683, hlam]
                                  · rcases p3676_3 (m.d 4 5) (by simp) with h3685 | h3685
                                    · linarith only [h3230, h3685, hlam]
                                    · linarith only [h3239, h3685, hlam]
                              · linarith only [h3233, h3680, hlam]
                            · linarith only [h3227, h3679, hlam]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            rcases p3676_3 (m.d 0 5) (by simp) with h3690 | h3690
                            · rcases p3676_3 (m.d 1 5) (by simp) with h3691 | h3691
                              · rcases p3676_3 (m.d 2 5) (by simp) with h3692 | h3692
                                · linarith only [h3227, h3692, hlam]
                                · linarith only [h3238, h3692, hlam]
                              · linarith only [h3235, h3691, hlam]
                            · linarith only [h3229, h3690, hlam]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3569_1, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p3676_1, u1ehi0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [hlam, p3676_0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            rcases p3676_3 (m.d 0 5) (by simp) with h3700 | h3700
                            · linarith only [h3223, h3700, hlam]
                            · linarith only [h3227, h3700, hlam]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            rcases p3676_3 (m.d 0 5) (by simp) with h3703 | h3703
                            · linarith only [h3223, h3703, hlam]
                            · linarith only [h3229, h3703, hlam]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3569_1, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3227, hlam, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3233, hlam, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [hlam, p3676_0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3239, hlam, p3676_0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3229, hlam, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3235, hlam, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3238, hlam, p3676_0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [hlam, p3676_0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3389, hlam, p3676_0]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3230, hlam, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3236, hlam, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3221, h3230, h3231, h3234, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [h3221, h3230, h3231, h3234, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3676_1]
                          · have p3676_0 := h3676c.1
                            have p3676_1 := h3676c.2.1
                            have p3676_2 := h3676c.2.2.1
                            have p3676_3 := h3676c.2.2.2
                            linarith only [hlam, p3676_0]
                        · linarith only [h3675, hlam, p3569_0]
                  · linarith only [h3232, h3670, hlam]
                · linarith only [h3226, h3669, hlam]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                rcases p3569_3 (m.d 0 4) (by simp) with h3725 | h3725
                · rcases p3569_3 (m.d 1 4) (by simp) with h3726 | h3726
                  · rcases p3569_3 (m.d 2 4) (by simp) with h3727 | h3727
                    · linarith only [h3239, h3727, hlam]
                    · linarith only [h3237, h3727, hlam]
                  · linarith only [h3234, h3726, hlam]
                · linarith only [h3228, h3725, hlam]
              · have p3569_0 := h3569c.1
                have p3569_1 := h3569c.2.1
                have p3569_2 := h3569c.2.2.1
                have p3569_3 := h3569c.2.2.2
                linarith only [hlam, p3569_0]
            · rcases h4bigk with h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c | h3733c
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3221, hlam, p3733_1]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3736 | h3736
                · rcases p3733_3 (m.d 1 4) (by simp) with h3737 | h3737
                  · rcases p3733_3 (m.d 2 4) (by simp) with h3738 | h3738
                    · linarith only [h3226, h3738, hlam]
                    · rcases p3733_3 (m.d 3 4) (by simp) with h3740 | h3740
                      · linarith only [h3228, h3740, hlam]
                      · rcases p3733_3 (m.d 4 5) (by simp) with h3742 | h3742
                        · linarith only [h3230, h3742, hlam]
                        · linarith only [h3239, h3742, hlam]
                  · linarith only [h3232, h3737, hlam]
                · linarith only [h3226, h3736, hlam]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3747 | h3747
                · rcases p3733_3 (m.d 1 4) (by simp) with h3748 | h3748
                  · rcases p3733_3 (m.d 2 4) (by simp) with h3749 | h3749
                    · linarith only [h3226, h3749, hlam]
                    · linarith only [h3237, h3749, hlam]
                  · linarith only [h3234, h3748, hlam]
                · linarith only [h3228, h3747, hlam]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3754 | h3754
                · rcases p3733_3 (m.d 1 4) (by simp) with h3755 | h3755
                  · rcases p3733_3 (m.d 2 4) (by simp) with h3756 | h3756
                    · linarith only [h3226, h3756, hlam]
                    · rcases p3733_3 (m.d 3 4) (by simp) with h3758 | h3758
                      · linarith only [h3228, h3758, hlam]
                      · rcases p3733_3 (m.d 4 5) (by simp) with h3760 | h3760
                        · linarith only [h3760, hlam, p3733_0]
                        · rcases h5bigk with h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c | h3762c
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [hlam, p3762_0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3223, hlam, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            rcases p3762_3 (m.d 0 5) (by simp) with h3765 | h3765
                            · rcases p3762_3 (m.d 1 5) (by simp) with h3766 | h3766
                              · rcases p3762_3 (m.d 2 5) (by simp) with h3767 | h3767
                                · linarith only [h3227, h3767, hlam]
                                · rcases p3762_3 (m.d 3 5) (by simp) with h3769 | h3769
                                  · linarith only [h3229, h3769, hlam]
                                  · rcases p3762_3 (m.d 4 5) (by simp) with h3771 | h3771
                                    · linarith only [h3230, h3771, hlam]
                                    · linarith only [h3239, h3771, hlam]
                              · linarith only [h3233, h3766, hlam]
                            · linarith only [h3227, h3765, hlam]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            rcases p3762_3 (m.d 0 5) (by simp) with h3776 | h3776
                            · rcases p3762_3 (m.d 1 5) (by simp) with h3777 | h3777
                              · rcases p3762_3 (m.d 2 5) (by simp) with h3778 | h3778
                                · linarith only [h3227, h3778, hlam]
                                · linarith only [h3238, h3778, hlam]
                              · linarith only [h3235, h3777, hlam]
                            · linarith only [h3229, h3776, hlam]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3230, hlam, p3733_2, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p3762_1, u1ehi0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [hlam, p3762_0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            rcases p3762_3 (m.d 0 5) (by simp) with h3786 | h3786
                            · linarith only [h3223, h3786, hlam]
                            · linarith only [h3227, h3786, hlam]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            rcases p3762_3 (m.d 0 5) (by simp) with h3789 | h3789
                            · linarith only [h3223, h3789, hlam]
                            · linarith only [h3229, h3789, hlam]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, h3239, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3227, hlam, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3233, hlam, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [hlam, p3762_0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3239, hlam, p3762_0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3229, hlam, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3235, hlam, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3238, hlam, p3762_0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [hlam, p3762_0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3389, hlam, p3762_0]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3230, hlam, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3236, hlam, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3221, h3231, h3234, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3733_1, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [h3221, h3231, h3234, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3733_1, p3762_1]
                          · have p3762_0 := h3762c.1
                            have p3762_1 := h3762c.2.1
                            have p3762_2 := h3762c.2.2.1
                            have p3762_3 := h3762c.2.2.2
                            linarith only [hlam, p3762_0]
                  · linarith only [h3236, h3755, hlam]
                · linarith only [h3754, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p3733_1, u1ehi0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3812 | h3812
                · linarith only [h3221, h3812, hlam]
                · linarith only [h3226, h3812, hlam]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3815 | h3815
                · linarith only [h3221, h3815, hlam]
                · linarith only [h3228, h3815, hlam]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3818 | h3818
                · linarith only [h3221, h3818, hlam]
                · linarith only [h3230, h3818, hlam]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3226, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3232, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3230, h3239, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3733_1]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3239, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3228, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3234, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3237, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3389, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3230, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [h3236, hlam, p3733_0]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3833 | h3833
                · rcases p3733_3 (m.d 1 4) (by simp) with h3834 | h3834
                  · rcases p3733_3 (m.d 2 4) (by simp) with h3835 | h3835
                    · linarith only [h3835, hlam, p3733_0]
                    · rcases p3733_3 (m.d 3 4) (by simp) with h3837 | h3837
                      · linarith only [h3389, h3837, hlam]
                      · rcases p3733_3 (m.d 4 5) (by simp) with h3839 | h3839
                        · rcases h5bigk with h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3223, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 5) (by simp) with h3843 | h3843
                            · rcases p3840_3 (m.d 1 5) (by simp) with h3844 | h3844
                              · rcases p3840_3 (m.d 2 5) (by simp) with h3845 | h3845
                                · linarith only [h3227, h3845, hlam]
                                · rcases p3840_3 (m.d 3 5) (by simp) with h3847 | h3847
                                  · linarith only [h3229, h3847, hlam]
                                  · rcases p3840_3 (m.d 4 5) (by simp) with h3849 | h3849
                                    · linarith only [h3230, h3849, hlam]
                                    · linarith only [h3239, h3849, hlam]
                              · linarith only [h3233, h3844, hlam]
                            · linarith only [h3227, h3843, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 5) (by simp) with h3854 | h3854
                            · rcases p3840_3 (m.d 1 5) (by simp) with h3855 | h3855
                              · rcases p3840_3 (m.d 2 5) (by simp) with h3856 | h3856
                                · linarith only [h3227, h3856, hlam]
                                · linarith only [h3238, h3856, hlam]
                              · linarith only [h3235, h3855, hlam]
                            · linarith only [h3229, h3854, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3733_1, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p3840_1, u1ehi0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 5) (by simp) with h3864 | h3864
                            · linarith only [h3223, h3864, hlam]
                            · linarith only [h3227, h3864, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 5) (by simp) with h3867 | h3867
                            · linarith only [h3223, h3867, hlam]
                            · linarith only [h3229, h3867, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3231, h3234, h3236, h3237, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3733_1, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3227, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3233, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h0, h3227, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3239, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3229, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3235, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3238, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3389, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3230, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3236, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3221, h3230, h3231, h3234, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3221, h3230, h3231, h3234, h3389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                        · linarith only [h3839, hlam, p3733_0]
                  · linarith only [h3232, h3834, hlam]
                · linarith only [h3226, h3833, hlam]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                rcases p3733_3 (m.d 0 4) (by simp) with h3889 | h3889
                · rcases p3733_3 (m.d 1 4) (by simp) with h3890 | h3890
                  · rcases p3733_3 (m.d 2 4) (by simp) with h3891 | h3891
                    · linarith only [h3239, h3891, hlam]
                    · linarith only [h3237, h3891, hlam]
                  · linarith only [h3234, h3890, hlam]
                · linarith only [h3228, h3889, hlam]
              · have p3733_0 := h3733c.1
                have p3733_1 := h3733c.2.1
                have p3733_2 := h3733c.2.2.1
                have p3733_3 := h3733c.2.2.2
                linarith only [hlam, p3733_0]
    · linarith only [h3231, h3395, hlam]
  · linarith only [h3394, hlam, p3391_0]

set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x0_x0_x1_x1_x3 (m : N7Model)
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
    (h3391c : ((m.d 0 2) < (m.d 2 4) ∧ 2 * m.lam ≤ (m.d 2 4) - (m.d 0 2) ∧ (m.d 2 4) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 2), (m.d 1 2), (m.d 2 3), (m.d 2 4), (m.d 2 5)], z ≤ (m.d 0 2) ∨ (m.d 2 4) ≤ z)))
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
  rcases p3391_3 (m.d 0 2) (by simp) with h3899 | h3899
  · rcases p3391_3 (m.d 1 2) (by simp) with h3900 | h3900
    · rcases p3391_3 (m.d 2 3) (by simp) with h3901 | h3901
      · linarith only [h3225, h3901, hlam]
      · linarith only [h3237, h3901, hlam]
    · linarith only [h3232, h3900, hlam]
  · linarith only [h3899, hlam, p3391_0]

end R2N4
