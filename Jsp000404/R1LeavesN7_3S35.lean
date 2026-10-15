import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S31
import Jsp000404.R1LeavesN7_3S32
import Jsp000404.R1LeavesN7_3S33
import Jsp000404.R1LeavesN7_3S34

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h22593 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h23332 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h23666 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 3 5 (by decide) (by decide) with h24291 | h24291
  · rcases m.htr 0 4 5 (by decide) (by decide) with h24292 | h24292
    · rcases m.htr 1 2 3 (by decide) (by decide) with h24293 | h24293
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24294 | h24294
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24295 | h24295
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24296 | h24296
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24297 | h24297
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24298 | h24298
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24299 | h24299
                  · linarith only [h23666, h24291, h24293, h24299, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h19110, h24293, h24296, h24299, hc01, hc12, hlam, hphi]
                · linarith only [h16563, h23666, h24291, h24292, h24293, h24296, h24298, hc01, hc12, hlam, hphi]
              · linarith only [h23666, h24296, h24297, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24304 | h24304
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24305 | h24305
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24306 | h24306
                  · linarith only [h24293, h24296, h24306, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24308 | h24308
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24309 | h24309
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24310 | h24310
                        · rcases h1bigk with h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c | h24311c
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h0, hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h14799, hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h16563, hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h17994, hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            rcases p24311_3 (m.d 0 1) (by simp) with h24317 | h24317
                            · linarith only [h24317, hlam, p24311_0]
                            · rcases p24311_3 (m.d 1 2) (by simp) with h24319 | h24319
                              · rcases p24311_3 (m.d 1 3) (by simp) with h24320 | h24320
                                · linarith only [h24293, h24320, hlam]
                                · linarith only [h14799, h24320, hlam]
                              · linarith only [h24319, hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h0, h23332, h24295, hc01, hc12, hlam, hphi, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24296, hc01, hc34, hlam, hphi, ht12, ht23, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24293, hlam, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24296, hlam, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h0, h23332, h24295, h24296, hc01, hc34, hlam, hphi, ht12, ht23, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            rcases p24311_3 (m.d 0 1) (by simp) with h24333 | h24333
                            · linarith only [h24333, hlam, p24311_0]
                            · rcases p24311_3 (m.d 1 2) (by simp) with h24335 | h24335
                              · rcases p24311_3 (m.d 1 3) (by simp) with h24336 | h24336
                                · linarith only [h24296, h24336, hlam]
                                · linarith only [h14799, h24336, hlam]
                              · linarith only [h0, h24335, hlam]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24294, hlam, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h14799, hc01, hc14, hlam, hphi, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h0, h23332, h24295, h24296, hc01, hc34, hlam, hphi, ht12, ht23, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24296, h24304, hc01, hc34, hlam, hphi, ht12, ht23, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24295, hlam, p24311_1]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24304, hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [h24305, hlam, p24311_0]
                          · have p24311_0 := h24311c.1
                            have p24311_1 := h24311c.2.1
                            have p24311_2 := h24311c.2.2.1
                            have p24311_3 := h24311c.2.2.2
                            linarith only [hlam, p24311_0]
                        · linarith only [h14799, h24296, h24310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h14799, h23332, h24291, h24292, h24296, h24306, h24308, h24309, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h19110, h24291, h24308, hlam]
                · linarith only [h16563, h22593, h24292, h24305, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h19110, h24291, h24293, h24304, hlam]
          · linarith only [h0, h22593, h24294, h24295, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h19110, h24293, h24294, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24356 | h24356
        · linarith only [h0, h22593, h24293, h24356, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24358 | h24358
          · linarith only [h0, h23332, h24293, h24358, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24360 | h24360
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24361 | h24361
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24362 | h24362
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24363 | h24363
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24364 | h24364
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24365 | h24365
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24366 | h24366
                        · rcases h1bigk with h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c | h24367c
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h0, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h14799, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h16563, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h17994, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h24358, h24363, h24365, hc01, hc23, hlam, hphi, ht12, p24367_1]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h24293, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h24356, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h24358, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            rcases p24367_3 (m.d 0 1) (by simp) with h24378 | h24378
                            · linarith only [h24378, hlam, p24367_0]
                            · rcases p24367_3 (m.d 1 2) (by simp) with h24380 | h24380
                              · linarith only [h24293, h24380, hlam]
                              · linarith only [h0, h24380, hlam]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h0, h24293, hc01, hc23, hlam, hphi, ht12, p24367_1]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h0, h24293, h24358, h24362, hc01, hc23, hlam, hphi, ht12, p24367_1]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h0, h24293, h24358, hc01, hc23, hlam, hphi, ht12, p24367_1]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            rcases p24367_3 (m.d 0 1) (by simp) with h24387 | h24387
                            · linarith only [h24387, hlam, p24367_0]
                            · rcases p24367_3 (m.d 1 2) (by simp) with h24389 | h24389
                              · linarith only [h24356, h24389, hlam]
                              · linarith only [h0, h24389, hlam]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p24367_1]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h24360, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h0, h24356, h24358, h24363, hc01, hc23, hlam, hphi, ht12, p24367_1]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            rcases p24367_3 (m.d 0 1) (by simp) with h24396 | h24396
                            · linarith only [h24396, hlam, p24367_0]
                            · rcases p24367_3 (m.d 1 2) (by simp) with h24398 | h24398
                              · linarith only [h24358, h24398, hlam]
                              · linarith only [h0, h24398, hlam]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p24367_1]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h24361, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [h24362, hlam, p24367_0]
                          · have p24367_0 := h24367c.1
                            have p24367_1 := h24367c.2.1
                            have p24367_2 := h24367c.2.2.1
                            have p24367_3 := h24367c.2.2.2
                            linarith only [hlam, p24367_0]
                        · linarith only [h23666, h24291, h24292, h24366, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h16563, h23666, h24291, h24292, h24356, h24365, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h23666, h24291, h24293, h24360, h24364, hlam]
                  · linarith only [h24293, h24360, h24363, hlam]
                · linarith only [h23666, h24291, h24292, h24360, h24362, hc04, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h23666, h24291, h24360, h24361, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24411 | h24411
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24412 | h24412
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24413 | h24413
                  · linarith only [h0, h24358, h24360, h24411, h24413, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h24293, h24413, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16563, h23666, h24291, h24292, h24412, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h14799, h24291, h24411, hlam]
    · linarith only [h23666, h24291, h24292, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h24419 | h24419
    · rcases m.htr 1 2 3 (by decide) (by decide) with h24420 | h24420
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24421 | h24421
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24422 | h24422
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24423 | h24423
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24424 | h24424
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24425 | h24425
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24426 | h24426
                  · linarith only [h14799, h23666, h24420, h24426, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h19110, h24420, h24423, h24426, hc01, hc12, hlam, hphi]
                · linarith only [h22593, h24419, h24421, h24425, hlam]
              · linarith only [h0, h19110, h23666, h24423, h24424, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24431 | h24431
              · linarith only [h0, h19110, h24291, h24423, h24431, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24433 | h24433
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24434 | h24434
                  · linarith only [h14799, h24423, h24434, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24436 | h24436
                    · linarith only [h24420, h24431, h24436, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24438 | h24438
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24439 | h24439
                        · rcases h1bigk with h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c | h24440c
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h0, hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h14799, hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h16563, hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h17994, hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            rcases p24440_3 (m.d 0 1) (by simp) with h24446 | h24446
                            · linarith only [h24446, hlam, p24440_0]
                            · rcases p24440_3 (m.d 1 2) (by simp) with h24448 | h24448
                              · rcases p24440_3 (m.d 1 3) (by simp) with h24449 | h24449
                                · linarith only [h24420, h24449, hlam]
                                · linarith only [h14799, h24449, hlam]
                              · linarith only [h24448, hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h0, h19110, h24420, hc01, hc12, hlam, hphi, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h24431, h24439, hc01, hc34, hlam, hphi, ht12, ht23, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h24420, hlam, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h24423, hlam, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h24431, hlam, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            rcases p24440_3 (m.d 0 1) (by simp) with h24462 | h24462
                            · linarith only [h24462, hlam, p24440_0]
                            · rcases p24440_3 (m.d 1 2) (by simp) with h24464 | h24464
                              · rcases p24440_3 (m.d 1 3) (by simp) with h24465 | h24465
                                · linarith only [h24423, h24465, hlam]
                                · linarith only [h14799, h24465, hlam]
                              · linarith only [h0, h24464, hlam]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h24421, hlam, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h0, h19110, h24420, hc01, hc14, hlam, hphi, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h0, h19110, h24420, h24423, h24431, hc01, hc34, hlam, hphi, ht12, ht23, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            rcases p24440_3 (m.d 0 1) (by simp) with h24473 | h24473
                            · linarith only [h24473, hlam, p24440_0]
                            · rcases p24440_3 (m.d 1 2) (by simp) with h24475 | h24475
                              · rcases p24440_3 (m.d 1 3) (by simp) with h24476 | h24476
                                · linarith only [h24431, h24476, hlam]
                                · linarith only [h14799, h24476, hlam]
                              · linarith only [h0, h24475, hlam]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h24422, hlam, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h0, h19110, h24420, hc01, hc15, hlam, hphi, p24440_1]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [h24433, hlam, p24440_0]
                          · have p24440_0 := h24440c.1
                            have p24440_1 := h24440c.2.1
                            have p24440_2 := h24440c.2.2.1
                            have p24440_3 := h24440c.2.2.2
                            linarith only [hlam, p24440_0]
                        · linarith only [h16563, h22593, h24419, h24423, h24439, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h22593, h24419, h24438, hlam]
                · linarith only [h16563, h22593, h24419, h24433, hc01, hc24, hlam, hphi, ht12]
          · linarith only [h0, h22593, h24421, h24422, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h19110, h24420, h24421, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24489 | h24489
        · linarith only [h0, h22593, h24420, h24489, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24491 | h24491
          · linarith only [h0, h23332, h24489, h24491, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24493 | h24493
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24494 | h24494
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24495 | h24495
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24496 | h24496
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24497 | h24497
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24498 | h24498
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24499 | h24499
                        · rcases h1bigk with h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h0, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h14799, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h16563, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h17994, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h24491, h24496, h24498, hc01, hc23, hlam, hphi, ht12, p24500_1]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h24420, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h24489, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h24491, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            rcases p24500_3 (m.d 0 1) (by simp) with h24511 | h24511
                            · linarith only [h24511, hlam, p24500_0]
                            · rcases p24500_3 (m.d 1 2) (by simp) with h24513 | h24513
                              · linarith only [h24420, h24513, hlam]
                              · linarith only [h0, h24513, hlam]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h0, h24420, hc01, hc23, hlam, hphi, ht12, p24500_1]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h16563, h24420, hc01, hc23, hlam, hphi, ht12, p24500_1]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h17994, h24420, hc01, hc23, hlam, hphi, ht12, p24500_1]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            rcases p24500_3 (m.d 0 1) (by simp) with h24520 | h24520
                            · linarith only [h24520, hlam, p24500_0]
                            · rcases p24500_3 (m.d 1 2) (by simp) with h24522 | h24522
                              · linarith only [h24489, h24522, hlam]
                              · linarith only [h0, h24522, hlam]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p24500_1]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h24493, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h0, h19110, h24291, h24489, h24494, h24496, hc01, hc23, hlam, hphi, ht12, p24500_1]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            rcases p24500_3 (m.d 0 1) (by simp) with h24529 | h24529
                            · linarith only [h24529, hlam, p24500_0]
                            · rcases p24500_3 (m.d 1 2) (by simp) with h24531 | h24531
                              · linarith only [h24491, h24531, hlam]
                              · linarith only [h0, h24531, hlam]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p24500_1]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h24494, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [h24495, hlam, p24500_0]
                          · have p24500_0 := h24500c.1
                            have p24500_1 := h24500c.2.1
                            have p24500_2 := h24500c.2.2.1
                            have p24500_3 := h24500c.2.2.2
                            linarith only [hlam, p24500_0]
                        · linarith only [h23666, h24419, h24499, hlam]
                      · linarith only [h16563, h23666, h24419, h24420, h24489, h24493, h24498, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h24420, h24494, h24495, h24497, hc01, hc14, hlam, hphi]
                  · linarith only [h0, h19110, h24291, h24420, h24494, h24496, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16563, h23666, h24419, h24493, h24495, hc01, hc13, hlam, hphi]
              · linarith only [h19110, h23666, h24493, h24494, hc02, hc35, hlam, hphi, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24544 | h24544
              · linarith only [h0, h19110, h24291, h24493, h24544, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24546 | h24546
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24547 | h24547
                  · linarith only [h14799, h24493, h24547, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h24420, h24547, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16563, h24419, h24546, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h24551 | h24551
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24552 | h24552
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24553 | h24553
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24554 | h24554
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24555 | h24555
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24556 | h24556
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24557 | h24557
                  · linarith only [h0, h19110, h23666, h24551, h24557, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h19110, h24554, h24557, hc01, hc13, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24560 | h24560
                  · linarith only [h0, h19110, h23666, h24551, h24560, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h19110, h24551, h24554, h24560, hc01, hc12, hlam, hphi]
              · linarith only [h0, h19110, h23666, h24554, h24555, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24564 | h24564
              · linarith only [h0, h19110, h24291, h24554, h24564, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24566 | h24566
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24567 | h24567
                  · linarith only [h14799, h24554, h24567, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24569 | h24569
                    · linarith only [h24551, h24564, h24569, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24571 | h24571
                      · linarith only [h0, h19110, h23666, h24419, h24552, h24571, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h22593, h24566, h24571, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24574 | h24574
                  · linarith only [h0, h19110, h23666, h24551, h24564, h24574, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24576 | h24576
                    · linarith only [h0, h19110, h24291, h24551, h24576, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24578 | h24578
                      · linarith only [h14799, h24554, h24566, h24578, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24580 | h24580
                        · linarith only [h0, h19110, h24551, h24554, h24566, h24580, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h19110, h24551, h24554, h24580, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h19110, h24551, h24553, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h19110, h24551, h24552, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24585 | h24585
        · linarith only [h0, h22593, h24551, h24585, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24587 | h24587
          · linarith only [h0, h23332, h24551, h24587, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24589 | h24589
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24590 | h24590
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24591 | h24591
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24592 | h24592
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24593 | h24593
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24594 | h24594
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24595 | h24595
                        · linarith only [h0, h19110, h23666, h24419, h24589, h24595, hc01, hc13, hlam, hphi]
                        · linarith only [h0, h19110, h23666, h24591, h24595, hc01, hc14, hlam, hphi]
                      · linarith only [h24585, h24591, h24594, hlam]
                    · linarith only [h24551, h24590, h24593, hlam]
                  · linarith only [h0, h19110, h24291, h24551, h24590, h24592, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24601 | h24601
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24602 | h24602
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24603 | h24603
                      · linarith only [h16563, h24591, h24603, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h24585, h24603, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h19110, h24590, h24602, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h19110, h24291, h24551, h24590, h24601, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h19110, h23666, h24589, h24590, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24609 | h24609
              · linarith only [h0, h19110, h24291, h24589, h24609, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24611 | h24611
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24612 | h24612
                  · linarith only [h14799, h24589, h24612, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h24551, h24612, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24615 | h24615
                  · linarith only [h0, h24551, h24589, h24615, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h24551, h24615, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h22593 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h23332 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 3 4 (by decide) (by decide) with h23666 | h23666
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110 h22593 h23332 h23666
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110 h22593 h23332 h23666

set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h22593 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 2 5 (by decide) (by decide) with h23332 | h23332
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110 h22593 h23332
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110 h22593 h23332

set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 2 4 (by decide) (by decide) with h22593 | h22593
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110 h22593
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110 h22593

set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 2 3 (by decide) (by decide) with h19110 | h19110
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110
  · exact r1l7_11_13_25_L_I_L_I_H_I_s16_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 h19110

end R2N4
