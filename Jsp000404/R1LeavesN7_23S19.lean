import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S15
import Jsp000404.R1LeavesN7_23S16
import Jsp000404.R1LeavesN7_23S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 1 5 (by decide) (by decide) with h4359 | h4359
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x0 m hb2 hb4 hg0 hg3260 h4130 h4359
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1 m hb2 hb4 hg0 hg3260 h4130 h4359

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 1 4 (by decide) (by decide) with h4130 | h4130
  · exact r1l7_12_24_L_I_M_IR_s3_x0 m hb2 hb4 hg0 hg3260 h4130
  · exact r1l7_12_24_L_I_M_IR_s3_x1 m hb2 hb4 hg0 hg3260 h4130

set_option maxHeartbeats 6912000 in
set_option maxHeartbeats 6912000 in
theorem r1l7_12_24_L_I_M_IR_s2 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h3260 | h3260
  · rcases m.htr 0 1 4 (by decide) (by decide) with h3261 | h3261
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3262 | h3262
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3263 | h3263
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3264 | h3264
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3265 | h3265
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3266 | h3266
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3267 | h3267
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3268 | h3268
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3269 | h3269
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3270 | h3270
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3271 | h3271
                        · linarith only [h0, h3260, h3271, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3273 | h3273
                          · linarith only [h0, h3261, h3273, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h3261, h3267, h3273, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h3260, h3266, h3270, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h3260, h3266, h3269, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h3260, h3266, h3267, h3268, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3279 | h3279
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3280 | h3280
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3281 | h3281
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3282 | h3282
                        · linarith only [h0, h3260, h3282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3284 | h3284
                          · linarith only [h0, h3261, h3267, h3284, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3286 | h3286
                            · linarith only [h3279, h3282, h3286, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3288 | h3288
                              · linarith only [h0, h3260, h3266, h3279, h3282, h3288, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3290 | h3290
                                · linarith only [h3261, h3266, h3267, h3279, h3280, h3282, h3290, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3292 | h3292
                                  · linarith only [h3266, h3267, h3292, hlam]
                                  · rcases h2bigk with h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c | h3294c
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h0, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      rcases p3294_3 (m.d 0 2) (by simp) with h3297 | h3297
                                      · rcases p3294_3 (m.d 1 2) (by simp) with h3298 | h3298
                                        · rcases p3294_3 (m.d 2 3) (by simp) with h3299 | h3299
                                          · linarith only [h3299, hlam, p3294_0]
                                          · rcases p3294_3 (m.d 2 4) (by simp) with h3301 | h3301
                                            · linarith only [h3264, h3301, hlam]
                                            · linarith only [h3286, h3301, hlam]
                                        · linarith only [h3279, h3298, hlam]
                                      · linarith only [h3297, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      rcases p3294_3 (m.d 0 2) (by simp) with h3306 | h3306
                                      · rcases p3294_3 (m.d 1 2) (by simp) with h3307 | h3307
                                        · rcases p3294_3 (m.d 2 3) (by simp) with h3308 | h3308
                                          · linarith only [h3263, h3308, hlam]
                                          · rcases p3294_3 (m.d 2 4) (by simp) with h3310 | h3310
                                            · linarith only [h3310, hlam, p3294_0]
                                            · rcases p3294_3 (m.d 2 5) (by simp) with h3312 | h3312
                                              · linarith only [h3265, h3312, hlam]
                                              · linarith only [h3290, h3312, hlam]
                                        · linarith only [h3280, h3307, hlam]
                                      · linarith only [h3306, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      rcases p3294_3 (m.d 0 2) (by simp) with h3317 | h3317
                                      · rcases p3294_3 (m.d 1 2) (by simp) with h3318 | h3318
                                        · rcases p3294_3 (m.d 2 3) (by simp) with h3319 | h3319
                                          · linarith only [h3263, h3319, hlam]
                                          · rcases p3294_3 (m.d 2 4) (by simp) with h3321 | h3321
                                            · linarith only [h3264, h3321, hlam]
                                            · rcases p3294_3 (m.d 2 5) (by simp) with h3323 | h3323
                                              · linarith only [h3323, hlam, p3294_0]
                                              · rcases h4bigk with h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c | h3325c
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3267, hc45, hlam, hphi, p3325_1, u4ehi1]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3267, hc45, hlam, hphi, p3325_1, u4ehi2]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3267, h3280, h3282, hc45, hlam, hphi, p3325_1, u4ehi2]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3267, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3261, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h0, h3260, h3266, h3282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3325_1, u4ehi2]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3282, hlam, p3325_1]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3284, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3264, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3280, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3286, hlam, p3325_1]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3290, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3266, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h0, h3260, h3266, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3325_1, u4ehi1]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h0, h3260, h3266, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3325_1, u4ehi2]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3292, hlam, p3325_0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [hc45, hlam, hphi, p3325_1, u4ehi0]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3280, hc45, hlam, hphi, p3325_1, u4ehi2]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [hc45, hlam, hphi, p3325_1, u4ehi2]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [h3279, h3282, hc23, hc45, hlam, hphi, ht34, p3325_1]
                                                · have p3325_0 := h3325c.1
                                                  have p3325_1 := h3325c.2.1
                                                  have p3325_2 := h3325c.2.2.1
                                                  have p3325_3 := h3325c.2.2.2
                                                  linarith only [hlam, p3325_0]
                                        · linarith only [h3281, h3318, hlam]
                                      · linarith only [h3317, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h0, h3261, h3280, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3294_1, u4ehi2]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h0, h3260, h3266, h3279, h3282, hlam, p3294_2]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      rcases p3294_3 (m.d 0 2) (by simp) with h3356 | h3356
                                      · linarith only [h0, h3356, hlam]
                                      · linarith only [h3264, h3356, hlam]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      rcases p3294_3 (m.d 0 2) (by simp) with h3359 | h3359
                                      · linarith only [h0, h3359, hlam]
                                      · linarith only [h3265, h3359, hlam]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3263, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3279, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3286, hlam, p3294_1]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3288, hlam, p3294_1]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3264, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3280, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h0, h3261, h3280, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3294_1]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3290, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3265, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h3281, hlam, p3294_0]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h0, h3262, h3281, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3294_1]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [h0, h3262, h3281, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3294_1, u4ehi2]
                                    · have p3294_0 := h3294c.1
                                      have p3294_1 := h3294c.2.1
                                      have p3294_2 := h3294c.2.2.1
                                      have p3294_3 := h3294c.2.2.2
                                      linarith only [hlam, p3294_0]
                      · linarith only [h0, h3260, h3266, h3281, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h3260, h3266, h3280, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h3260, h3266, h3279, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3380 | h3380
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3381 | h3381
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3382 | h3382
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3383 | h3383
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3384 | h3384
                        · linarith only [h0, h3260, h3266, h3384, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3386 | h3386
                          · linarith only [h0, h3261, h3386, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h3261, h3380, h3386, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h3261, h3382, h3383, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h3261, h3382, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h3261, h3380, h3381, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3392 | h3392
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3393 | h3393
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3394 | h3394
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3395 | h3395
                        · linarith only [h3260, h3266, h3395, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3397 | h3397
                          · linarith only [h0, h3261, h3380, h3397, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3399 | h3399
                            · linarith only [h3260, h3266, h3380, h3392, h3399, hc45, hlam, hphi, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3401 | h3401
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3402 | h3402
                                · linarith only [h3261, h3380, h3393, h3402, hlam]
                                · linarith only [h3399, h3401, h3402, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3405 | h3405
                                · linarith only [h0, h3264, h3380, h3405, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3407 | h3407
                                  · rcases h2bigk with h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c | h3408c
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h0, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      rcases p3408_3 (m.d 0 2) (by simp) with h3411 | h3411
                                      · rcases p3408_3 (m.d 1 2) (by simp) with h3412 | h3412
                                        · rcases p3408_3 (m.d 2 3) (by simp) with h3413 | h3413
                                          · linarith only [h3413, hlam, p3408_0]
                                          · rcases p3408_3 (m.d 2 4) (by simp) with h3415 | h3415
                                            · linarith only [h3264, h3415, hlam]
                                            · linarith only [h3399, h3415, hlam]
                                        · linarith only [h3392, h3412, hlam]
                                      · linarith only [h3411, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      rcases p3408_3 (m.d 0 2) (by simp) with h3420 | h3420
                                      · rcases p3408_3 (m.d 1 2) (by simp) with h3421 | h3421
                                        · rcases p3408_3 (m.d 2 3) (by simp) with h3422 | h3422
                                          · linarith only [h3263, h3422, hlam]
                                          · rcases p3408_3 (m.d 2 4) (by simp) with h3424 | h3424
                                            · linarith only [h3424, hlam, p3408_0]
                                            · rcases p3408_3 (m.d 2 5) (by simp) with h3426 | h3426
                                              · linarith only [h3265, h3426, hlam]
                                              · linarith only [h3405, h3426, hlam]
                                        · linarith only [h3393, h3421, hlam]
                                      · linarith only [h3420, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      rcases p3408_3 (m.d 0 2) (by simp) with h3431 | h3431
                                      · rcases p3408_3 (m.d 1 2) (by simp) with h3432 | h3432
                                        · rcases p3408_3 (m.d 2 3) (by simp) with h3433 | h3433
                                          · linarith only [h3263, h3433, hlam]
                                          · rcases p3408_3 (m.d 2 4) (by simp) with h3435 | h3435
                                            · linarith only [h3264, h3435, hlam]
                                            · rcases p3408_3 (m.d 2 5) (by simp) with h3437 | h3437
                                              · linarith only [h3437, hlam, p3408_0]
                                              · rcases h4bigk with h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c | h3439c
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3380, h3407, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3439_1, u4ehi1]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3380, h3407, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3439_1, u4ehi2]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3266, hlam, p3439_1]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3380, hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3261, hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3262, h3397, hc01, hlam, hphi, ht0b, ht45, ht5b, p3439_1, u4ehi2]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3395, hlam, p3439_1]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3397, hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3264, hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3393, hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3399, hlam, p3439_1]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3405, hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  rcases p3439_3 (m.d 0 4) (by simp) with h3455 | h3455
                                                  · linarith only [h3266, h3455, hlam]
                                                  · rcases p3439_3 (m.d 1 4) (by simp) with h3457 | h3457
                                                    · linarith only [h3395, h3457, hlam]
                                                    · rcases p3439_3 (m.d 2 4) (by simp) with h3459 | h3459
                                                      · linarith only [h3399, h3459, hlam]
                                                      · rcases p3439_3 (m.d 3 4) (by simp) with h3461 | h3461
                                                        · rcases p3439_3 (m.d 4 5) (by simp) with h3462 | h3462
                                                          · linarith only [h3407, h3462, hlam]
                                                          · linarith only [h3380, h3462, hlam]
                                                        · linarith only [h3266, h3461, hlam]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  rcases p3439_3 (m.d 0 4) (by simp) with h3466 | h3466
                                                  · linarith only [h3266, h3466, hlam]
                                                  · linarith only [h3261, h3466, hlam]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  rcases p3439_3 (m.d 0 4) (by simp) with h3469 | h3469
                                                  · linarith only [h3266, h3469, hlam]
                                                  · linarith only [h3264, h3469, hlam]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3380, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3439_1, u4ehi0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3261, hc45, hlam, hphi, p3439_1, u4ehi1]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3393, hc45, hlam, hphi, p3439_1, u4ehi2]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [hc45, hlam, hphi, p3439_1, u4ehi2]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [h3407, hlam, p3439_0]
                                                · have p3439_0 := h3439c.1
                                                  have p3439_1 := h3439c.2.1
                                                  have p3439_2 := h3439c.2.2.1
                                                  have p3439_3 := h3439c.2.2.2
                                                  linarith only [hlam, p3439_0]
                                        · linarith only [h3394, h3432, hlam]
                                      · linarith only [h3431, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h0, h3261, h3393, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3408_1, u4ehi2]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      rcases p3408_3 (m.d 0 2) (by simp) with h3483 | h3483
                                      · linarith only [h0, h3483, hlam]
                                      · linarith only [h3263, h3483, hlam]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      rcases p3408_3 (m.d 0 2) (by simp) with h3486 | h3486
                                      · linarith only [h0, h3486, hlam]
                                      · linarith only [h3264, h3486, hlam]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      rcases p3408_3 (m.d 0 2) (by simp) with h3489 | h3489
                                      · linarith only [h0, h3489, hlam]
                                      · linarith only [h3265, h3489, hlam]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3263, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3392, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3399, hlam, p3408_1]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3401, hlam, p3408_1]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3264, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3393, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h0, h3262, h3394, h3405, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3408_1]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3405, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3265, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h3394, hlam, p3408_0]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h0, h3261, h3262, h3380, h3393, h3394, h3407, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3408_1, u4ehi2]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [h0, h3262, h3394, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3408_1, u4ehi2]
                                    · have p3408_0 := h3408c.1
                                      have p3408_1 := h3408c.2.1
                                      have p3408_2 := h3408c.2.2.1
                                      have p3408_3 := h3408c.2.2.2
                                      linarith only [hlam, p3408_0]
                                  · rcases h2bigk with h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c | h3507c
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h0, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      rcases p3507_3 (m.d 0 2) (by simp) with h3510 | h3510
                                      · rcases p3507_3 (m.d 1 2) (by simp) with h3511 | h3511
                                        · rcases p3507_3 (m.d 2 3) (by simp) with h3512 | h3512
                                          · linarith only [h3512, hlam, p3507_0]
                                          · rcases p3507_3 (m.d 2 4) (by simp) with h3514 | h3514
                                            · linarith only [h3264, h3514, hlam]
                                            · linarith only [h3399, h3514, hlam]
                                        · linarith only [h3392, h3511, hlam]
                                      · linarith only [h3510, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      rcases p3507_3 (m.d 0 2) (by simp) with h3519 | h3519
                                      · rcases p3507_3 (m.d 1 2) (by simp) with h3520 | h3520
                                        · rcases p3507_3 (m.d 2 3) (by simp) with h3521 | h3521
                                          · linarith only [h3263, h3521, hlam]
                                          · rcases p3507_3 (m.d 2 4) (by simp) with h3523 | h3523
                                            · linarith only [h3523, hlam, p3507_0]
                                            · rcases p3507_3 (m.d 2 5) (by simp) with h3525 | h3525
                                              · linarith only [h3265, h3525, hlam]
                                              · linarith only [h3405, h3525, hlam]
                                        · linarith only [h3393, h3520, hlam]
                                      · linarith only [h3519, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      rcases p3507_3 (m.d 0 2) (by simp) with h3530 | h3530
                                      · rcases p3507_3 (m.d 1 2) (by simp) with h3531 | h3531
                                        · rcases p3507_3 (m.d 2 3) (by simp) with h3532 | h3532
                                          · linarith only [h3263, h3532, hlam]
                                          · rcases p3507_3 (m.d 2 4) (by simp) with h3534 | h3534
                                            · linarith only [h3264, h3534, hlam]
                                            · rcases p3507_3 (m.d 2 5) (by simp) with h3536 | h3536
                                              · linarith only [h3536, hlam, p3507_0]
                                              · rcases h4bigk with h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c | h3538c
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h0, h3261, h3393, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3538_1, u4ehi2]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h0, h3261, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3538_1, u4ehi2]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3266, hlam, p3538_1]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3380, hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3261, hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h0, h3261, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3538_1, u4ehi2]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3395, hlam, p3538_1]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3397, hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3264, hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3393, hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3399, hlam, p3538_1]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3405, hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3407, hc45, hlam, hphi, p3538_1, u4ehi0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3407, hc45, hlam, hphi, p3538_1, u4ehi1]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3407, hc45, hlam, hphi, p3538_1, u4ehi2]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3407, hlam, p3538_0]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3261, h3393, hc45, hlam, hphi, p3538_1, u4ehi2]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3393, hc45, hlam, hphi, p3538_1, u4ehi2]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [hc45, hlam, hphi, p3538_1, u4ehi2]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [h3266, hc03, hc45, hlam, hphi, ht34, p3538_1]
                                                · have p3538_0 := h3538c.1
                                                  have p3538_1 := h3538c.2.1
                                                  have p3538_2 := h3538c.2.2.1
                                                  have p3538_3 := h3538c.2.2.2
                                                  linarith only [hlam, p3538_0]
                                        · linarith only [h3394, h3531, hlam]
                                      · linarith only [h3530, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h0, h3261, h3393, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3507_1, u4ehi2]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      rcases p3507_3 (m.d 0 2) (by simp) with h3568 | h3568
                                      · linarith only [h0, h3568, hlam]
                                      · linarith only [h3263, h3568, hlam]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      rcases p3507_3 (m.d 0 2) (by simp) with h3571 | h3571
                                      · linarith only [h0, h3571, hlam]
                                      · linarith only [h3264, h3571, hlam]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      rcases p3507_3 (m.d 0 2) (by simp) with h3574 | h3574
                                      · linarith only [h0, h3574, hlam]
                                      · linarith only [h3265, h3574, hlam]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3263, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3392, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3399, hlam, p3507_1]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3401, hlam, p3507_1]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3264, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3393, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h0, h3262, h3393, h3397, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3507_1]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3405, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3265, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h3394, hlam, p3507_0]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h0, h3262, h3394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3507_1]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [h0, h3262, h3394, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3507_1, u4ehi2]
                                    · have p3507_0 := h3507c.1
                                      have p3507_1 := h3507c.2.1
                                      have p3507_2 := h3507c.2.2.1
                                      have p3507_3 := h3507c.2.2.2
                                      linarith only [hlam, p3507_0]
                      · linarith only [h0, h3261, h3394, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h3261, h3393, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h3261, h3392, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h3262, h3265, hlam]
          · linarith only [h0, h3261, h3264, hlam]
        · linarith only [h0, h3260, h3263, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3598 | h3598
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3599 | h3599
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3600 | h3600
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3601 | h3601
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3602 | h3602
                · linarith only [h3260, h3262, h3601, h3602, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3604 | h3604
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3605 | h3605
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3606 | h3606
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3607 | h3607
                        · linarith only [h3260, h3262, h3606, h3607, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3609 | h3609
                          · linarith only [h3261, h3262, h3602, h3606, h3609, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h3260, h3262, h3601, h3604, h3607, h3609, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3260, h3600, h3601, h3606, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h3260, h3601, h3605, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h3260, h3601, h3604, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3615 | h3615
                · linarith only [h3261, h3262, h3615, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3617 | h3617
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3618 | h3618
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3619 | h3619
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3620 | h3620
                        · linarith only [h3260, h3262, h3601, h3619, h3620, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3622 | h3622
                          · linarith only [h3261, h3262, h3615, h3619, h3622, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h3261, h3262, h3622, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h0, h3261, h3600, h3618, h3619, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h3261, h3618, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h3261, h3617, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3628 | h3628
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3629 | h3629
                · linarith only [h0, h3260, h3600, h3628, h3629, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3631 | h3631
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3632 | h3632
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3633 | h3633
                      · linarith only [h0, h3260, h3600, h3628, h3633, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h3260, h3628, h3633, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h3260, h3628, h3632, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h3260, h3628, h3631, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3638 | h3638
                · linarith only [h0, h3261, h3600, h3638, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3640 | h3640
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3641 | h3641
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3642 | h3642
                      · linarith only [h0, h3261, h3600, h3642, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h3261, h3641, h3642, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h3261, h3641, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h3261, h3640, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h3261, h3599, hlam]
        · linarith only [h0, h3260, h3598, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3649 | h3649
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3650 | h3650
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3651 | h3651
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3652 | h3652
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3653 | h3653
              · linarith only [h3260, h3261, h3653, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3655 | h3655
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3656 | h3656
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3657 | h3657
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3658 | h3658
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3659 | h3659
                        · linarith only [h3260, h3261, h3653, h3657, h3659, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3661 | h3661
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3662 | h3662
                            · linarith only [h3260, h3261, h3656, h3659, h3662, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3664 | h3664
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3665 | h3665
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3666 | h3666
                                  · linarith only [h3260, h3261, h3656, h3659, h3664, h3666, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                  · linarith only [h3261, h3651, h3659, h3665, h3666, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · linarith only [h3261, h3649, h3661, h3665, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3670 | h3670
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3671 | h3671
                                  · rcases h2bigk with h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c | h3672c
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h0, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      rcases p3672_3 (m.d 0 2) (by simp) with h3675 | h3675
                                      · rcases p3672_3 (m.d 1 2) (by simp) with h3676 | h3676
                                        · rcases p3672_3 (m.d 2 3) (by simp) with h3677 | h3677
                                          · linarith only [h3677, hlam, p3672_0]
                                          · rcases p3672_3 (m.d 2 4) (by simp) with h3679 | h3679
                                            · linarith only [h3651, h3679, hlam]
                                            · linarith only [h3662, h3679, hlam]
                                        · linarith only [h3656, h3676, hlam]
                                      · linarith only [h3675, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3670, hc02, hlam, hphi, ht0b, ht45, ht5b, p3672_1, u4ehi4]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      rcases p3672_3 (m.d 0 2) (by simp) with h3685 | h3685
                                      · rcases p3672_3 (m.d 1 2) (by simp) with h3686 | h3686
                                        · rcases p3672_3 (m.d 2 3) (by simp) with h3687 | h3687
                                          · linarith only [h3650, h3687, hlam]
                                          · rcases p3672_3 (m.d 2 4) (by simp) with h3689 | h3689
                                            · linarith only [h3651, h3689, hlam]
                                            · linarith only [h3670, h3689, hlam]
                                        · linarith only [h3658, h3686, hlam]
                                      · linarith only [h3685, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3651, h3670, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3672_1, u4ehi4]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      rcases p3672_3 (m.d 0 2) (by simp) with h3696 | h3696
                                      · linarith only [h0, h3696, hlam]
                                      · linarith only [h3650, h3696, hlam]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3670, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3672_1, u4ehi4]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      rcases p3672_3 (m.d 0 2) (by simp) with h3700 | h3700
                                      · linarith only [h0, h3700, hlam]
                                      · linarith only [h3652, h3700, hlam]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3650, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3656, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3662, hlam, p3672_1]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3664, hlam, p3672_1]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3651, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3657, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      rcases p3672_3 (m.d 0 2) (by simp) with h3710 | h3710
                                      · rcases p3672_3 (m.d 1 2) (by simp) with h3711 | h3711
                                        · rcases p3672_3 (m.d 2 3) (by simp) with h3712 | h3712
                                          · linarith only [h3662, h3712, hlam]
                                          · rcases p3672_3 (m.d 2 4) (by simp) with h3714 | h3714
                                            · rcases p3672_3 (m.d 2 5) (by simp) with h3715 | h3715
                                              · linarith only [h3670, h3715, hlam]
                                              · linarith only [h3664, h3715, hlam]
                                            · linarith only [h3662, h3714, hlam]
                                        · linarith only [h3656, h3711, hlam]
                                      · linarith only [h3650, h3710, hlam]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h0, h3651, h3670, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3672_1, u4ehi4]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3652, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3658, hlam, p3672_0]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3261, h3649, h3652, h3659, hc23, hc34, hlam, hphi, p3672_1]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [h3670, hlam, p3672_1]
                                    · have p3672_0 := h3672c.1
                                      have p3672_1 := h3672c.2.1
                                      have p3672_2 := h3672c.2.2.1
                                      have p3672_3 := h3672c.2.2.2
                                      linarith only [hlam, p3672_0]
                                  · linarith only [h3261, h3649, h3658, h3659, h3670, h3671, hlam]
                                · linarith only [h3261, h3649, h3659, h3661, h3670, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h3260, h3261, h3655, h3661, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3652, h3658, hlam]
                    · linarith only [h0, h3651, h3657, hlam]
                  · linarith only [h0, h3650, h3656, hlam]
                · linarith only [h3261, h3649, h3655, hlam]
            · linarith only [h0, h3649, h3652, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3736 | h3736
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3737 | h3737
              · linarith only [h0, h3260, h3651, h3737, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3739 | h3739
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3740 | h3740
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3741 | h3741
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3742 | h3742
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3743 | h3743
                        · linarith only [h0, h3260, h3651, h3737, h3741, h3743, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3745 | h3745
                          · linarith only [h0, h3649, h3651, h3741, h3745, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h3260, h3651, h3739, h3741, h3745, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3260, h3651, h3740, h3741, h3742, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3749 | h3749
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3750 | h3750
                        · linarith only [h0, h3260, h3737, h3741, h3750, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3752 | h3752
                          · linarith only [h0, h3649, h3741, h3752, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h3260, h3739, h3740, h3741, h3752, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3260, h3736, h3740, h3749, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3650, h3740, hlam]
                · linarith only [h0, h3649, h3651, h3739, hlam]
            · linarith only [h0, h3649, h3736, hlam]
        · linarith only [h0, h3260, h3650, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3760 | h3760
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3761 | h3761
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3762 | h3762
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3763 | h3763
              · linarith only [h3260, h3261, h3763, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3765 | h3765
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3766 | h3766
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3767 | h3767
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3768 | h3768
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3769 | h3769
                        · linarith only [h3260, h3261, h3763, h3767, h3769, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3771 | h3771
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3772 | h3772
                            · linarith only [h3260, h3649, h3766, h3769, h3771, h3772, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3774 | h3774
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3775 | h3775
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3776 | h3776
                                  · linarith only [h3260, h3649, h3766, h3769, h3771, h3774, h3776, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                  · linarith only [h3649, h3761, h3769, h3771, h3775, h3776, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · linarith only [h3772, h3774, h3775, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3780 | h3780
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3781 | h3781
                                  · rcases h2bigk with h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h0, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      rcases p3782_3 (m.d 0 2) (by simp) with h3785 | h3785
                                      · rcases p3782_3 (m.d 1 2) (by simp) with h3786 | h3786
                                        · rcases p3782_3 (m.d 2 3) (by simp) with h3787 | h3787
                                          · linarith only [h3787, hlam, p3782_0]
                                          · rcases p3782_3 (m.d 2 4) (by simp) with h3789 | h3789
                                            · linarith only [h3761, h3789, hlam]
                                            · linarith only [h3772, h3789, hlam]
                                        · linarith only [h3766, h3786, hlam]
                                      · linarith only [h3785, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h0, h3780, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3782_1, u4ehi4]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      rcases p3782_3 (m.d 0 2) (by simp) with h3795 | h3795
                                      · rcases p3782_3 (m.d 1 2) (by simp) with h3796 | h3796
                                        · rcases p3782_3 (m.d 2 3) (by simp) with h3797 | h3797
                                          · linarith only [h3760, h3797, hlam]
                                          · rcases p3782_3 (m.d 2 4) (by simp) with h3799 | h3799
                                            · linarith only [h3761, h3799, hlam]
                                            · linarith only [h3780, h3799, hlam]
                                        · linarith only [h3768, h3796, hlam]
                                      · linarith only [h3795, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3761, h3780, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3782_1, u4ehi4]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      rcases p3782_3 (m.d 0 2) (by simp) with h3806 | h3806
                                      · linarith only [h0, h3806, hlam]
                                      · linarith only [h3760, h3806, hlam]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3780, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3782_1, u4ehi4]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      rcases p3782_3 (m.d 0 2) (by simp) with h3810 | h3810
                                      · linarith only [h0, h3810, hlam]
                                      · linarith only [h3762, h3810, hlam]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3760, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3766, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3772, hlam, p3782_1]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3774, hlam, p3782_1]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3761, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3767, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      rcases p3782_3 (m.d 0 2) (by simp) with h3820 | h3820
                                      · rcases p3782_3 (m.d 1 2) (by simp) with h3821 | h3821
                                        · rcases p3782_3 (m.d 2 3) (by simp) with h3822 | h3822
                                          · linarith only [h3772, h3822, hlam]
                                          · rcases p3782_3 (m.d 2 4) (by simp) with h3824 | h3824
                                            · rcases p3782_3 (m.d 2 5) (by simp) with h3825 | h3825
                                              · linarith only [h3780, h3825, hlam]
                                              · linarith only [h3774, h3825, hlam]
                                            · linarith only [h3772, h3824, hlam]
                                        · linarith only [h3766, h3821, hlam]
                                      · linarith only [h3760, h3820, hlam]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h0, h3761, h3780, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3782_1, u4ehi4]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3762, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3768, hlam, p3782_0]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      rcases p3782_3 (m.d 0 2) (by simp) with h3835 | h3835
                                      · rcases p3782_3 (m.d 1 2) (by simp) with h3836 | h3836
                                        · rcases p3782_3 (m.d 2 3) (by simp) with h3837 | h3837
                                          · linarith only [h3774, h3837, hlam]
                                          · rcases p3782_3 (m.d 2 4) (by simp) with h3839 | h3839
                                            · rcases p3782_3 (m.d 2 5) (by simp) with h3840 | h3840
                                              · rcases h4bigk with h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3261, hlam, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3261, h3780, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3782_1, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3763, hlam, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  rcases p3841_3 (m.d 0 4) (by simp) with h3846 | h3846
                                                  · rcases p3841_3 (m.d 1 4) (by simp) with h3847 | h3847
                                                    · rcases p3841_3 (m.d 2 4) (by simp) with h3848 | h3848
                                                      · linarith only [h3761, h3848, hlam]
                                                      · linarith only [h3780, h3848, hlam]
                                                    · linarith only [h3771, h3847, hlam]
                                                  · linarith only [h3846, hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3260, h3261, h3766, h3769, hc23, hc34, hlam, hphi, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3769, h3780, hc23, hc34, hlam, hphi, p3782_1, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3769, hlam, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  rcases p3841_3 (m.d 0 4) (by simp) with h3857 | h3857
                                                  · linarith only [h3261, h3857, hlam]
                                                  · linarith only [h3765, h3857, hlam]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3761, hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3767, hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3772, hlam, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h0, h3761, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3841_1, u4ehi4]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3761, h3780, hc23, hc34, hlam, hphi, p3782_1, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3260, h3261, h3766, hc23, hc34, hlam, hphi, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3780, hc23, hc34, hlam, hphi, p3782_1, p3841_1]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  rcases p3841_3 (m.d 0 4) (by simp) with h3869 | h3869
                                                  · linarith only [h3763, h3869, hlam]
                                                  · linarith only [h3765, h3869, hlam]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3765, hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3771, hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3780, hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [h3781, hlam, p3841_0]
                                                · have p3841_0 := h3841c.1
                                                  have p3841_1 := h3841c.2.1
                                                  have p3841_2 := h3841c.2.2.1
                                                  have p3841_3 := h3841c.2.2.2
                                                  linarith only [hlam, p3841_0]
                                              · linarith only [h3774, h3840, hlam]
                                            · linarith only [h3772, h3839, hlam]
                                        · linarith only [h3766, h3836, hlam]
                                      · linarith only [h3760, h3835, hlam]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [h3780, hlam, p3782_1]
                                    · have p3782_0 := h3782c.1
                                      have p3782_1 := h3782c.2.1
                                      have p3782_2 := h3782c.2.2.1
                                      have p3782_3 := h3782c.2.2.2
                                      linarith only [hlam, p3782_0]
                                  · linarith only [h3763, h3765, h3781, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3884 | h3884
                                  · rcases h2bigk with h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c | h3885c
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h0, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      rcases p3885_3 (m.d 0 2) (by simp) with h3888 | h3888
                                      · rcases p3885_3 (m.d 1 2) (by simp) with h3889 | h3889
                                        · rcases p3885_3 (m.d 2 3) (by simp) with h3890 | h3890
                                          · linarith only [h3890, hlam, p3885_0]
                                          · rcases p3885_3 (m.d 2 4) (by simp) with h3892 | h3892
                                            · linarith only [h3761, h3892, hlam]
                                            · linarith only [h3772, h3892, hlam]
                                        · linarith only [h3766, h3889, hlam]
                                      · linarith only [h3888, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      rcases p3885_3 (m.d 0 2) (by simp) with h3897 | h3897
                                      · rcases p3885_3 (m.d 1 2) (by simp) with h3898 | h3898
                                        · rcases p3885_3 (m.d 2 3) (by simp) with h3899 | h3899
                                          · linarith only [h3760, h3899, hlam]
                                          · rcases p3885_3 (m.d 2 4) (by simp) with h3901 | h3901
                                            · linarith only [h3901, hlam, p3885_0]
                                            · rcases p3885_3 (m.d 2 5) (by simp) with h3903 | h3903
                                              · linarith only [h3762, h3903, hlam]
                                              · linarith only [h3780, h3903, hlam]
                                        · linarith only [h3767, h3898, hlam]
                                      · linarith only [h3897, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      rcases p3885_3 (m.d 0 2) (by simp) with h3908 | h3908
                                      · rcases p3885_3 (m.d 1 2) (by simp) with h3909 | h3909
                                        · rcases p3885_3 (m.d 2 3) (by simp) with h3910 | h3910
                                          · linarith only [h3760, h3910, hlam]
                                          · rcases p3885_3 (m.d 2 4) (by simp) with h3912 | h3912
                                            · linarith only [h3761, h3912, hlam]
                                            · rcases p3885_3 (m.d 2 5) (by simp) with h3914 | h3914
                                              · linarith only [h3914, hlam, p3885_0]
                                              · rcases h4bigk with h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3261, hlam, p3916_1]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  rcases p3916_3 (m.d 0 4) (by simp) with h3919 | h3919
                                                  · rcases p3916_3 (m.d 1 4) (by simp) with h3920 | h3920
                                                    · rcases p3916_3 (m.d 2 4) (by simp) with h3921 | h3921
                                                      · linarith only [h3761, h3921, hlam]
                                                      · rcases p3916_3 (m.d 3 4) (by simp) with h3923 | h3923
                                                        · rcases p3916_3 (m.d 4 5) (by simp) with h3924 | h3924
                                                          · linarith only [h3765, h3924, hlam]
                                                          · linarith only [h3780, h3924, hlam]
                                                        · linarith only [h3772, h3923, hlam]
                                                    · linarith only [h3767, h3920, hlam]
                                                  · linarith only [h3761, h3919, hlam]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3763, hlam, p3916_1]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3761, h3780, hc02, hlam, hphi, ht0b, ht45, ht5b, p3916_1, u4ehi2]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3260, h3261, h3769, hc13, hc34, hlam, hphi, p3916_1]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  rcases p3916_3 (m.d 0 4) (by simp) with h3934 | h3934
                                                  · linarith only [h3261, h3934, hlam]
                                                  · linarith only [h3761, h3934, hlam]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3769, hlam, p3916_1]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3769, h3780, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3916_1, u4ehi2]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3761, hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3767, hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3772, hlam, p3916_1]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3780, hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3765, h3780, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3916_1, u4ehi2]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3260, h3261, h3766, hc23, hc34, hlam, hphi, p3916_1]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  rcases p3916_3 (m.d 0 4) (by simp) with h3946 | h3946
                                                  · linarith only [h3763, h3946, hlam]
                                                  · linarith only [h3761, h3946, hlam]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3780, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3916_1, u4ehi2]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3765, hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3771, hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3765, hc04, hlam, hphi, ht0b, ht45, ht5b, p3916_1, u4ehi2]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [h3884, hlam, p3916_0]
                                                · have p3916_0 := h3916c.1
                                                  have p3916_1 := h3916c.2.1
                                                  have p3916_2 := h3916c.2.2.1
                                                  have p3916_3 := h3916c.2.2.2
                                                  linarith only [hlam, p3916_0]
                                        · linarith only [h3768, h3909, hlam]
                                      · linarith only [h3908, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3761, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3885_1, u4ehi2]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      rcases p3885_3 (m.d 0 2) (by simp) with h3960 | h3960
                                      · linarith only [h0, h3960, hlam]
                                      · linarith only [h3760, h3960, hlam]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      rcases p3885_3 (m.d 0 2) (by simp) with h3963 | h3963
                                      · linarith only [h0, h3963, hlam]
                                      · linarith only [h3761, h3963, hlam]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      rcases p3885_3 (m.d 0 2) (by simp) with h3966 | h3966
                                      · linarith only [h0, h3966, hlam]
                                      · linarith only [h3762, h3966, hlam]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3760, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3766, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3772, hlam, p3885_1]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3774, hlam, p3885_1]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3761, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3767, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3761, h3765, h3780, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3885_1]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3780, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3762, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3768, hlam, p3885_0]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3261, h3765, h3769, h3780, hc23, hc34, hlam, hphi, p3885_1]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [h3261, h3765, h3769, h3780, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3885_1, u4ehi2]
                                    · have p3885_0 := h3885c.1
                                      have p3885_1 := h3885c.2.1
                                      have p3885_2 := h3885c.2.2.1
                                      have p3885_3 := h3885c.2.2.2
                                      linarith only [hlam, p3885_0]
                                  · linarith only [h3261, h3765, h3769, h3884, hlam]
                          · linarith only [h3261, h3765, h3771, hlam]
                      · linarith only [h0, h3762, h3768, hlam]
                    · linarith only [h0, h3761, h3767, hlam]
                  · linarith only [h0, h3760, h3766, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3989 | h3989
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3990 | h3990
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3991 | h3991
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3992 | h3992
                        · linarith only [h3260, h3261, h3763, h3992, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3994 | h3994
                          · linarith only [h3260, h3261, h3765, h3992, h3994, hc13, hc34, hlam, hphi]
                          · linarith only [h3260, h3261, h3989, h3994, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3762, h3991, hlam]
                    · linarith only [h0, h3761, h3990, hlam]
                  · linarith only [h0, h3260, h3760, h3989, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4000 | h4000
              · linarith only [h3260, h3261, h4000, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4002 | h4002
                · linarith only [h3761, h3762, h4002, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4004 | h4004
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4005 | h4005
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4006 | h4006
                      · linarith only [h3761, h3762, h4006, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4008 | h4008
                        · linarith only [h3260, h3261, h4000, h4002, h4008, hc03, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4010 | h4010
                          · linarith only [h4002, h4005, h4006, h4010, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                          · linarith only [h3260, h3261, h4004, h4010, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3260, h3761, h4004, h4005, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3760, h4004, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4015 | h4015
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4016 | h4016
              · linarith only [h0, h3260, h3761, h4016, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4018 | h4018
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4019 | h4019
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4020 | h4020
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4021 | h4021
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4022 | h4022
                        · linarith only [h3260, h3649, h3761, h4015, h4016, h4020, h4022, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4024 | h4024
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4025 | h4025
                            · linarith only [h3260, h3649, h3761, h4015, h4019, h4020, h4022, h4025, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4027 | h4027
                              · linarith only [h3260, h3649, h3761, h4015, h4019, h4020, h4027, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4029 | h4029
                                · linarith only [h3761, h4015, h4020, h4029, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h3260, h3649, h3761, h4015, h4018, h4029, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h3761, h4015, h4018, h4020, h4024, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h3761, h4015, h4020, h4021, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4034 | h4034
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4035 | h4035
                        · linarith only [h0, h3260, h4016, h4020, h4035, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4037 | h4037
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4038 | h4038
                            · linarith only [h3260, h3261, h3649, h3761, h4019, h4020, h4034, h4035, h4038, hc02, hc24, hlam, hphi]
                            · linarith only [h3260, h3649, h4019, h4020, h4034, h4038, hc23, hc34, hlam, hphi]
                          · linarith only [h3260, h3649, h4018, h4019, h4020, h4034, h4037, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h4015, h4034, hlam]
                  · linarith only [h0, h3760, h4019, hlam]
                · linarith only [h3761, h4015, h4018, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4045 | h4045
              · linarith only [h0, h3260, h3761, h4045, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4047 | h4047
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4048 | h4048
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4049 | h4049
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4050 | h4050
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4051 | h4051
                        · linarith only [h0, h3260, h3761, h4045, h4049, h4051, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4053 | h4053
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4054 | h4054
                            · linarith only [h0, h3260, h3761, h4048, h4049, h4051, h4054, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4056 | h4056
                              · linarith only [h0, h3260, h3761, h4048, h4049, h4056, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4058 | h4058
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4059 | h4059
                                  · rcases h2bigk with h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h0, hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4015, h4049, h4058, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h3761, hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4015, hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      rcases p4060_3 (m.d 0 2) (by simp) with h4066 | h4066
                                      · linarith only [h0, h4066, hlam]
                                      · rcases p4060_3 (m.d 1 2) (by simp) with h4068 | h4068
                                        · rcases p4060_3 (m.d 2 3) (by simp) with h4069 | h4069
                                          · linarith only [h4048, h4069, hlam]
                                          · rcases p4060_3 (m.d 2 4) (by simp) with h4071 | h4071
                                            · linarith only [h4049, h4071, hlam]
                                            · linarith only [h3761, h4071, hlam]
                                        · linarith only [h0, h4068, hlam]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h3760, h4015, h4049, h4058, hlam, p4060_2]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h0, h4015, h4058, hc01, hc12, hlam, hphi, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h0, h3260, h4015, h4048, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h3760, hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4048, hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4054, hlam, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4056, hlam, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h0, h3260, h4048, h4049, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4049, hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      rcases p4060_3 (m.d 0 2) (by simp) with h4086 | h4086
                                      · linarith only [h3761, h4086, hlam]
                                      · linarith only [h3760, h4086, hlam]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h0, h3260, h4015, h4048, h4049, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h0, h3260, h4048, h4056, hc23, hc35, hlam, hphi, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4050, hlam, p4060_0]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      rcases p4060_3 (m.d 0 2) (by simp) with h4093 | h4093
                                      · linarith only [h4015, h4093, hlam]
                                      · linarith only [h3760, h4093, hlam]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [h4058, hlam, p4060_1]
                                    · have p4060_0 := h4060c.1
                                      have p4060_1 := h4060c.2.1
                                      have p4060_2 := h4060c.2.2.1
                                      have p4060_3 := h4060c.2.2.2
                                      linarith only [hlam, p4060_0]
                                  · linarith only [h3260, h3261, h4047, h4048, h4051, h4059, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · linarith only [h3761, h4047, h4058, hlam]
                          · linarith only [h3761, h4047, h4049, h4053, hlam]
                      · linarith only [h3761, h4047, h4049, h4050, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4102 | h4102
                      · linarith only [h0, h3260, h4015, h4048, h4049, h4102, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4104 | h4104
                        · linarith only [h0, h3260, h4049, h4104, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4106 | h4106
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4107 | h4107
                            · linarith only [h0, h3260, h4048, h4102, h4104, h4106, h4107, hlam]
                            · linarith only [h0, h3260, h4048, h4049, h4107, hc23, hc34, hlam, hphi]
                          · linarith only [h3260, h3261, h4047, h4048, h4106, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3260, h3760, h4048, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4112 | h4112
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4113 | h4113
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4114 | h4114
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4115 | h4115
                        · linarith only [h0, h3260, h4115, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4117 | h4117
                          · linarith only [h3260, h3261, h4047, h4112, h4115, h4117, hc23, hc34, hlam, hphi]
                          · linarith only [h3260, h3261, h4112, h4117, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3260, h3761, h4112, h4113, h4114, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4121 | h4121
                      · linarith only [h0, h3260, h4015, h4112, h4113, h4121, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4123 | h4123
                        · linarith only [h0, h3260, h4113, h4123, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4125 | h4125
                          · linarith only [h0, h3260, h3761, h4047, h4112, h4123, h4125, hc23, hc34, hlam, hphi]
                          · linarith only [h3260, h3261, h4112, h4125, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h3260, h3760, h4112, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h3260, h3760, hlam]
  · exact r1l7_12_24_L_I_M_IR_s3 m hb2 hb4 h0 h3260

set_option maxHeartbeats 13432000 in
set_option maxHeartbeats 13432000 in
theorem r1l7_12_24_L_I_M_IR (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_24_L_I_M_IR_s0 m hb2 hb4 h0
  · exact r1l7_12_24_L_I_M_IR_s2 m hb2 hb4 h0

end R2N4
