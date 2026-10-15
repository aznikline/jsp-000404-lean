import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S77

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8790000 in
set_option maxHeartbeats 8790000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s41 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  rcases m.htr 0 2 5 (by decide) (by decide) with h41029 | h41029
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s42 m hb1 hb2 hb4 hb5 h0 h33187 h36828 h39227 h41027 h41028 h41029
  · rcases m.htr 0 3 4 (by decide) (by decide) with h45274 | h45274
    · rcases m.htr 0 3 5 (by decide) (by decide) with h45275 | h45275
      · linarith only [h41027, h41029, h45275, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h45277 | h45277
        · linarith only [h41027, h41029, h45274, h45277, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h45279 | h45279
          · rcases m.htr 1 2 4 (by decide) (by decide) with h45280 | h45280
            · rcases m.htr 1 2 5 (by decide) (by decide) with h45281 | h45281
              · rcases m.htr 1 3 4 (by decide) (by decide) with h45282 | h45282
                · rcases m.htr 1 3 5 (by decide) (by decide) with h45283 | h45283
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h45284 | h45284
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45285 | h45285
                      · linarith only [h41027, h41029, h45281, h45285, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h41027, h41029, h45274, h45281, h45285, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45288 | h45288
                      · linarith only [h41027, h41029, h45281, h45288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h41027, h41029, h45274, h45281, h45288, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h45291 | h45291
                    · linarith only [h36828, h45277, h45282, h45283, h45291, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45293 | h45293
                      · linarith only [h41027, h41029, h45281, h45293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h41027, h41029, h45274, h45281, h45293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h41027, h41029, h45274, h45281, h45282, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h45297 | h45297
                · rcases m.htr 1 3 5 (by decide) (by decide) with h45298 | h45298
                  · linarith only [h45274, h45275, h45279, h45281, h45298, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h45300 | h45300
                    · linarith only [h36828, h45277, h45280, h45281, h45300, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45302 | h45302
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h45303 | h45303
                        · linarith only [h0, h41027, h45281, h45298, h45303, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h45305 | h45305
                          · linarith only [h41028, h45277, h45305, hlam]
                          · linarith only [h0, h41027, h45281, h45302, h45305, hc34, hc45, hlam, hphi]
                      · linarith only [h45274, h45275, h45302, hc23, hc35, hlam, hphi]
                · linarith only [h33187, h45274, h45297, hlam]
            · linarith only [h0, h41028, h45280, hlam]
          · linarith only [h0, h41027, h45279, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h45312 | h45312
      · linarith only [h41027, h41029, h45312, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h45314 | h45314
        · linarith only [h41028, h41029, h45314, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h45316 | h45316
          · rcases m.htr 1 2 4 (by decide) (by decide) with h45317 | h45317
            · rcases m.htr 1 2 5 (by decide) (by decide) with h45318 | h45318
              · rcases m.htr 1 3 4 (by decide) (by decide) with h45319 | h45319
                · rcases m.htr 1 3 5 (by decide) (by decide) with h45320 | h45320
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h45321 | h45321
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45322 | h45322
                      · linarith only [h41027, h41029, h45274, h45322, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h45324 | h45324
                        · linarith only [h39227, h41027, h41029, h45312, h45318, h45324, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h45326 | h45326
                          · linarith only [h41028, h41029, h45316, h45320, h45324, h45326, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h45328 | h45328
                            · linarith only [h41028, h41029, h45322, h45326, h45328, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h45274, h45316, h45319, h45321, h45328, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45331 | h45331
                      · linarith only [h33187, h41027, h41029, h45274, h45331, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h45333 | h45333
                        · linarith only [h41028, h41029, h45312, h45318, h45331, h45333, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h45335 | h45335
                          · linarith only [h41028, h41029, h45316, h45320, h45321, h45333, h45335, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h45337 | h45337
                            · linarith only [h45319, h45321, h45337, hlam]
                            · rcases h1bigk with h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c | h45339c
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h0, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h33187, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h36828, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h39227, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                rcases p45339_3 (m.d 0 1) (by simp) with h45345 | h45345
                                · linarith only [h45345, hlam, p45339_0]
                                · rcases p45339_3 (m.d 1 2) (by simp) with h45347 | h45347
                                  · rcases p45339_3 (m.d 1 3) (by simp) with h45348 | h45348
                                    · linarith only [h45316, h45348, hlam]
                                    · linarith only [h33187, h45348, hlam]
                                  · linarith only [h45347, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h41028, h41029, h45320, h45331, h45333, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h33187, h45274, h45319, hc01, hc12, hlam, hphi, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h39227, hc01, hc12, hlam, hphi, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                rcases p45339_3 (m.d 0 1) (by simp) with h45356 | h45356
                                · linarith only [h45356, hlam, p45339_0]
                                · rcases p45339_3 (m.d 1 2) (by simp) with h45358 | h45358
                                  · rcases p45339_3 (m.d 1 3) (by simp) with h45359 | h45359
                                    · rcases p45339_3 (m.d 1 4) (by simp) with h45360 | h45360
                                      · linarith only [h45319, h45360, hlam]
                                      · linarith only [h36828, h45360, hlam]
                                    · linarith only [h45359, hlam, p45339_0]
                                  · linarith only [h0, h45358, hlam]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h45316, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h33187, h45274, h45319, hc01, hc13, hlam, hphi, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h41028, h41029, h45316, h45320, h45331, h45333, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h45321, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h45317, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h45319, hlam, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h45321, hlam, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                rcases p45339_3 (m.d 0 1) (by simp) with h45374 | h45374
                                · linarith only [h45374, hlam, p45339_0]
                                · rcases p45339_3 (m.d 1 2) (by simp) with h45376 | h45376
                                  · rcases p45339_3 (m.d 1 3) (by simp) with h45377 | h45377
                                    · rcases p45339_3 (m.d 1 4) (by simp) with h45378 | h45378
                                      · linarith only [h45321, h45378, hlam]
                                      · linarith only [h36828, h45378, hlam]
                                    · linarith only [h33187, h45377, hlam]
                                  · linarith only [h0, h45376, hlam]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h45318, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h45320, hlam, p45339_0]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [h36828, hc01, hc15, hlam, hphi, p45339_1]
                              · have p45339_0 := h45339c.1
                                have p45339_1 := h45339c.2.1
                                have p45339_2 := h45339c.2.2.1
                                have p45339_3 := h45339c.2.2.2
                                linarith only [hlam, p45339_0]
                  · linarith only [h33187, h45274, h45319, h45320, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h45388 | h45388
                  · linarith only [h33187, h45312, h45319, h45388, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h45390 | h45390
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45391 | h45391
                      · linarith only [h33187, h45319, h45391, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h45393 | h45393
                        · linarith only [h41028, h41029, h45318, h45388, h45391, h45393, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h45395 | h45395
                          · linarith only [h33187, h41028, h41029, h45274, h45314, h45318, h45395, hc01, hc12, hlam, hphi]
                          · linarith only [h41028, h41029, h45319, h45390, h45391, h45395, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45398 | h45398
                      · linarith only [h41027, h41029, h45318, h45398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h45400 | h45400
                        · linarith only [h41028, h41029, h45318, h45398, h45400, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h45402 | h45402
                          · linarith only [h41028, h41029, h45318, h45390, h45402, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h45404 | h45404
                            · linarith only [h41028, h41029, h45318, h45390, h45398, h45404, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h45319, h45404, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h45407 | h45407
                · linarith only [h33187, h45274, h45316, h45318, h45407, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h45409 | h45409
                  · linarith only [h33187, h45312, h45317, h45318, h45407, h45409, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h45411 | h45411
                    · linarith only [h33187, h45274, h45314, h45317, h45318, h45411, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45413 | h45413
                      · linarith only [h33187, h45407, h45413, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h45415 | h45415
                        · linarith only [h33187, h39227, h41027, h45407, h45409, h45415, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h45417 | h45417
                          · linarith only [h0, h41028, h45274, h45314, h45318, h45415, h45417, hc03, hc35, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h45419 | h45419
                            · linarith only [h0, h45318, h45417, h45419, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h33187, h45407, h45419, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h41028, h45317, hlam]
          · linarith only [h0, h41027, h45316, hlam]

set_option maxHeartbeats 9928000 in
set_option maxHeartbeats 9928000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s40 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  rcases m.htr 0 2 4 (by decide) (by decide) with h41028 | h41028
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s41 m hb1 hb2 hb4 hb5 h0 h33187 h36828 h39227 h41027 h41028
  · rcases m.htr 0 2 5 (by decide) (by decide) with h45424 | h45424
    · rcases m.htr 0 3 4 (by decide) (by decide) with h45425 | h45425
      · linarith only [h41027, h41028, h45425, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h45427 | h45427
        · rcases m.htr 0 4 5 (by decide) (by decide) with h45428 | h45428
          · rcases m.htr 1 2 3 (by decide) (by decide) with h45429 | h45429
            · rcases m.htr 1 2 4 (by decide) (by decide) with h45430 | h45430
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45431 | h45431
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45432 | h45432
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45433 | h45433
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45434 | h45434
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45435 | h45435
                        · linarith only [h41027, h41028, h45425, h45430, h45435, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45437 | h45437
                          · linarith only [h41027, h41028, h45429, h45432, h45435, h45437, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h41027, h41028, h45427, h45429, h45432, h45435, h45437, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h41028, h45424, h45428, h45430, h45434, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h45425, h45427, h45432, h45433, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45442 | h45442
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45443 | h45443
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45444 | h45444
                        · linarith only [h41027, h41028, h45430, h45432, h45444, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45446 | h45446
                          · linarith only [h41027, h41028, h45430, h45446, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h33187, h45427, h45432, h45446, hc23, hc34, hlam, hphi]
                      · linarith only [h41027, h41028, h45430, h45443, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h41027, h41028, h45427, h45430, h45442, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h41028, h45430, h45431, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45452 | h45452
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45453 | h45453
                  · linarith only [h45425, h45427, h45429, h45430, h45453, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45455 | h45455
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45456 | h45456
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45457 | h45457
                        · linarith only [h0, h41027, h45430, h45453, h45457, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45459 | h45459
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45460 | h45460
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45461 | h45461
                              · rcases h1bigk with h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c | h45462c
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h0, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h33187, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h36828, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h39227, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45430, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h39227, h45430, h45455, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45430, hlam, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h39227, h45430, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45429, h45430, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45429, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45453, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h39227, h45429, h45430, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  rcases p45462_3 (m.d 0 1) (by simp) with h45478 | h45478
                                  · linarith only [h45478, hlam, p45462_0]
                                  · rcases p45462_3 (m.d 1 2) (by simp) with h45480 | h45480
                                    · linarith only [h45430, h45480, hlam]
                                    · linarith only [h0, h45480, hlam]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h0, h45430, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h33187, h45430, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h39227, h45430, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45429, h45430, h45455, h45457, hc01, hc34, hlam, hphi, ht12, ht23, p45462_1]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45452, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45455, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [h45456, hlam, p45462_0]
                                · have p45462_0 := h45462c.1
                                  have p45462_1 := h45462c.2.1
                                  have p45462_2 := h45462c.2.2.1
                                  have p45462_3 := h45462c.2.2.2
                                  linarith only [hlam, p45462_0]
                              · linarith only [h0, h45430, h45457, h45461, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h41027, h45427, h45428, h45430, h45459, h45460, hc03, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h33187, h45427, h45429, h45430, h45457, h45459, hc23, hc34, hlam, hphi]
                      · linarith only [h33187, h36828, h45427, h45428, h45453, h45456, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h33187, h45427, h45455, hlam]
                · linarith only [h0, h36828, h41028, h45424, h45452, hc01, hc14, hlam, hphi]
            · linarith only [h0, h41027, h45429, hlam]
          · linarith only [h41027, h41028, h45427, h45428, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h45500 | h45500
          · rcases m.htr 1 2 3 (by decide) (by decide) with h45501 | h45501
            · rcases m.htr 1 2 4 (by decide) (by decide) with h45502 | h45502
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45503 | h45503
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45504 | h45504
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45505 | h45505
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45506 | h45506
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45507 | h45507
                        · linarith only [h33187, h41027, h41028, h45425, h45502, h45507, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45509 | h45509
                          · linarith only [h33187, h41027, h41028, h45427, h45501, h45504, h45507, h45509, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45511 | h45511
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45512 | h45512
                              · rcases h1bigk with h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c | h45513c
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h0, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h33187, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h36828, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h39227, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  rcases p45513_3 (m.d 0 1) (by simp) with h45519 | h45519
                                  · linarith only [h45519, hlam, p45513_0]
                                  · rcases p45513_3 (m.d 1 2) (by simp) with h45521 | h45521
                                    · rcases p45513_3 (m.d 1 3) (by simp) with h45522 | h45522
                                      · linarith only [h45501, h45522, hlam]
                                      · linarith only [h33187, h45522, hlam]
                                    · linarith only [h45521, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h41028, h45424, h45504, h45507, h45509, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45513_1]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h36828, hc01, hc12, hlam, hphi, p45513_1]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h39227, hc01, hc12, hlam, hphi, p45513_1]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  rcases p45513_3 (m.d 0 1) (by simp) with h45530 | h45530
                                  · linarith only [h45530, hlam, p45513_0]
                                  · rcases p45513_3 (m.d 1 2) (by simp) with h45532 | h45532
                                    · rcases p45513_3 (m.d 1 3) (by simp) with h45533 | h45533
                                      · rcases p45513_3 (m.d 1 4) (by simp) with h45534 | h45534
                                        · linarith only [h45504, h45534, hlam]
                                        · linarith only [h36828, h45534, hlam]
                                      · linarith only [h45533, hlam, p45513_0]
                                    · linarith only [h0, h45532, hlam]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h45501, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h41028, h45424, h45504, h45507, h45509, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45513_1]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h33187, h45427, h45501, h45505, hc01, hc12, hlam, hphi, p45513_1]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  rcases p45513_3 (m.d 0 1) (by simp) with h45543 | h45543
                                  · linarith only [h45543, hlam, p45513_0]
                                  · rcases p45513_3 (m.d 1 2) (by simp) with h45545 | h45545
                                    · rcases p45513_3 (m.d 1 3) (by simp) with h45546 | h45546
                                      · rcases p45513_3 (m.d 1 4) (by simp) with h45547 | h45547
                                        · rcases p45513_3 (m.d 1 5) (by simp) with h45548 | h45548
                                          · linarith only [h45506, h45548, hlam]
                                          · linarith only [h39227, h45548, hlam]
                                        · linarith only [h45547, hlam, p45513_0]
                                      · linarith only [h33187, h45546, hlam]
                                    · linarith only [h0, h45545, hlam]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h45502, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h45504, hlam, p45513_1]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h33187, h45427, h45505, hc01, hc14, hlam, hphi, p45513_1]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  rcases p45513_3 (m.d 0 1) (by simp) with h45558 | h45558
                                  · linarith only [h45558, hlam, p45513_0]
                                  · rcases p45513_3 (m.d 1 2) (by simp) with h45560 | h45560
                                    · rcases p45513_3 (m.d 1 3) (by simp) with h45561 | h45561
                                      · rcases p45513_3 (m.d 1 4) (by simp) with h45562 | h45562
                                        · rcases p45513_3 (m.d 1 5) (by simp) with h45563 | h45563
                                          · rcases h1emax with h45564 | h45564 | h45564 | h45564 | h45564
                                            · rcases h2bigk with h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c | h45565c
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h0, hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41028, h45507, hc23, hc34, hlam, hphi, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41028, hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41028, h45507, h45509, hc23, hc34, hlam, hphi, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                rcases p45565_3 (m.d 0 2) (by simp) with h45571 | h45571
                                                · linarith only [h0, h45571, hlam]
                                                · rcases p45565_3 (m.d 1 2) (by simp) with h45573 | h45573
                                                  · rcases p45565_3 (m.d 2 3) (by simp) with h45574 | h45574
                                                    · linarith only [h45501, h45574, hlam]
                                                    · rcases p45565_3 (m.d 2 4) (by simp) with h45576 | h45576
                                                      · linarith only [h45502, h45576, hlam]
                                                      · linarith only [h41028, h45576, hlam]
                                                  · linarith only [h0, h45573, hlam]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41027, h41028, h45501, h45504, h45507, hlam, p45565_2]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41028, h45424, h45509, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41028, h45424, h45502, hlam, p45565_2]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41027, hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45501, hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45507, hlam, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45509, hlam, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45424, h45502, h45509, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45502, hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                rcases p45565_3 (m.d 0 2) (by simp) with h45591 | h45591
                                                · linarith only [h41028, h45591, hlam]
                                                · linarith only [h41027, h45591, hlam]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                rcases p45565_3 (m.d 0 2) (by simp) with h45595 | h45595
                                                · linarith only [h41028, h45595, hlam]
                                                · linarith only [h45424, h45595, hlam]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45424, hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45503, hlam, p45565_0]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h41028, h45424, h45501, h45504, h45507, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [h45511, hlam, p45565_1]
                                              · have p45565_0 := h45565c.1
                                                have p45565_1 := h45565c.2.1
                                                have p45565_2 := h45565c.2.2.1
                                                have p45565_3 := h45565c.2.2.2
                                                linarith only [hlam, p45565_0]
                                            · linarith only [h41028, h45501, h45504, h45507, h45564, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                            · linarith only [h41028, h45424, h45504, h45507, h45509, h45564, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                            · linarith only [h36828, h45564, hc01, hlam]
                                            · linarith only [h45564, hc01, hlam, p45513_1]
                                          · linarith only [h45563, hlam, p45513_0]
                                        · linarith only [h36828, h45562, hlam]
                                      · linarith only [h33187, h45561, hlam]
                                    · linarith only [h0, h45560, hlam]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h45503, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h45505, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [h45506, hlam, p45513_0]
                                · have p45513_0 := h45513c.1
                                  have p45513_1 := h45513c.2.1
                                  have p45513_2 := h45513c.2.2.1
                                  have p45513_3 := h45513c.2.2.2
                                  linarith only [hlam, p45513_0]
                              · linarith only [h41028, h45424, h45507, h45511, h45512, hlam]
                            · linarith only [h41028, h45424, h45509, h45511, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h36828, h45500, h45506, hlam]
                    · linarith only [h41027, h41028, h45425, h45504, h45505, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45619 | h45619
                    · linarith only [h33187, h45427, h45504, h45619, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45621 | h45621
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45622 | h45622
                        · linarith only [h41027, h41028, h45502, h45504, h45622, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45624 | h45624
                          · linarith only [h41027, h41028, h45502, h45619, h45624, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45626 | h45626
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45627 | h45627
                              · rcases h1bigk with h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c | h45628c
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h0, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h33187, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h36828, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h39227, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  rcases p45628_3 (m.d 0 1) (by simp) with h45634 | h45634
                                  · linarith only [h45634, hlam, p45628_0]
                                  · rcases p45628_3 (m.d 1 2) (by simp) with h45636 | h45636
                                    · rcases p45628_3 (m.d 1 3) (by simp) with h45637 | h45637
                                      · linarith only [h45501, h45637, hlam]
                                      · linarith only [h33187, h45637, hlam]
                                    · linarith only [h45636, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h33187, hc01, hc12, hlam, hphi, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h41028, h45424, h45502, h45624, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h33187, h45619, hc01, hc12, hlam, hphi, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h45619, hc01, hc35, hlam, hphi, ht12, ht23, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h45501, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h45504, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h45619, hlam, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  rcases p45628_3 (m.d 0 1) (by simp) with h45650 | h45650
                                  · linarith only [h45650, hlam, p45628_0]
                                  · rcases p45628_3 (m.d 1 2) (by simp) with h45652 | h45652
                                    · rcases p45628_3 (m.d 1 3) (by simp) with h45653 | h45653
                                      · linarith only [h45504, h45653, hlam]
                                      · linarith only [h33187, h45653, hlam]
                                    · linarith only [h0, h45652, hlam]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h45502, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h33187, hc01, hc14, hlam, hphi, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h33187, h45504, h45619, hc01, hc34, hlam, hphi, ht12, ht23, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  rcases p45628_3 (m.d 0 1) (by simp) with h45661 | h45661
                                  · linarith only [h45661, hlam, p45628_0]
                                  · rcases p45628_3 (m.d 1 2) (by simp) with h45663 | h45663
                                    · rcases p45628_3 (m.d 1 3) (by simp) with h45664 | h45664
                                      · linarith only [h45619, h45664, hlam]
                                      · linarith only [h33187, h45664, hlam]
                                    · linarith only [h0, h45663, hlam]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h45503, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h33187, hc01, hc15, hlam, hphi, p45628_1]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [h45621, hlam, p45628_0]
                                · have p45628_0 := h45628c.1
                                  have p45628_1 := h45628c.2.1
                                  have p45628_2 := h45628c.2.2.1
                                  have p45628_3 := h45628c.2.2.2
                                  linarith only [hlam, p45628_0]
                              · linarith only [h36828, h41028, h45424, h45504, h45626, h45627, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h41028, h45424, h45624, h45626, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h41028, h45424, h45500, h45502, h45621, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h41027, h41028, h45502, h45503, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45676 | h45676
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45677 | h45677
                  · linarith only [h33187, h45425, h45501, h45502, h45677, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45679 | h45679
                    · linarith only [h45427, h45677, h45679, hc03, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45681 | h45681
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45682 | h45682
                        · linarith only [h33187, h45677, h45682, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45684 | h45684
                          · linarith only [h33187, h41027, h45679, h45684, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45686 | h45686
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45687 | h45687
                              · rcases h1bigk with h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c | h45688c
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h0, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h33187, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h36828, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h39227, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45502, h45682, hc01, hc34, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h33187, h45502, h45682, hc01, hc34, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45502, hlam, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h39227, h45502, h45682, hc01, hc34, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45679, hc01, hc35, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45501, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45677, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45679, hlam, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  rcases p45688_3 (m.d 0 1) (by simp) with h45704 | h45704
                                  · linarith only [h45704, hlam, p45688_0]
                                  · rcases p45688_3 (m.d 1 2) (by simp) with h45706 | h45706
                                    · linarith only [h45502, h45706, hlam]
                                    · linarith only [h0, h45706, hlam]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h0, h45424, h45502, h45682, h45684, hc23, hc34, hlam, hphi, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h33187, h45502, h45682, hc01, hc34, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h33187, h45502, h45679, h45682, hc01, hc34, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45502, h45676, h45682, hc01, hc34, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45676, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h33187, h45502, h45676, h45682, hc01, hc34, hlam, hphi, ht12, ht23, p45688_1]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [h45681, hlam, p45688_0]
                                · have p45688_0 := h45688c.1
                                  have p45688_1 := h45688c.2.1
                                  have p45688_2 := h45688c.2.2.1
                                  have p45688_3 := h45688c.2.2.2
                                  linarith only [hlam, p45688_0]
                              · linarith only [h0, h45424, h45502, h45682, h45686, h45687, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · linarith only [h33187, h45502, h45676, h45679, h45686, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h36828, h45424, h45500, h45502, h45681, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h45424, h45676, hlam]
            · linarith only [h0, h41027, h45501, hlam]
          · linarith only [h41028, h45424, h45500, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h45724 | h45724
      · linarith only [h41027, h41028, h45724, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h45726 | h45726
        · linarith only [h41027, h45424, h45726, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h45728 | h45728
          · rcases m.htr 1 2 3 (by decide) (by decide) with h45729 | h45729
            · rcases m.htr 1 2 4 (by decide) (by decide) with h45730 | h45730
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45731 | h45731
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45732 | h45732
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45733 | h45733
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45734 | h45734
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45735 | h45735
                        · linarith only [h41027, h41028, h45724, h45730, h45735, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45737 | h45737
                          · linarith only [h33187, h41027, h41028, h45726, h45729, h45732, h45735, h45737, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45739 | h45739
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45740 | h45740
                              · rcases h1bigk with h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c | h45741c
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h0, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h33187, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h36828, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h39227, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  rcases p45741_3 (m.d 0 1) (by simp) with h45747 | h45747
                                  · linarith only [h45747, hlam, p45741_0]
                                  · rcases p45741_3 (m.d 1 2) (by simp) with h45749 | h45749
                                    · rcases p45741_3 (m.d 1 3) (by simp) with h45750 | h45750
                                      · linarith only [h45729, h45750, hlam]
                                      · linarith only [h33187, h45750, hlam]
                                    · linarith only [h45749, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h41027, h45424, h45732, h45735, h45739, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45741_1]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h41027, h45424, h45733, h45734, h45737, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45741_1]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h41027, h45424, h45733, h45737, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45741_1]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  rcases p45741_3 (m.d 0 1) (by simp) with h45758 | h45758
                                  · linarith only [h45758, hlam, p45741_0]
                                  · rcases p45741_3 (m.d 1 2) (by simp) with h45760 | h45760
                                    · rcases p45741_3 (m.d 1 3) (by simp) with h45761 | h45761
                                      · rcases p45741_3 (m.d 1 4) (by simp) with h45762 | h45762
                                        · linarith only [h45732, h45762, hlam]
                                        · linarith only [h36828, h45762, hlam]
                                      · linarith only [h45761, hlam, p45741_0]
                                    · linarith only [h0, h45760, hlam]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h45729, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h41027, h45424, h45733, h45734, h45737, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45741_1]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h41027, h45424, h45729, h45733, h45737, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45741_1]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  rcases p45741_3 (m.d 0 1) (by simp) with h45771 | h45771
                                  · linarith only [h45771, hlam, p45741_0]
                                  · rcases p45741_3 (m.d 1 2) (by simp) with h45773 | h45773
                                    · rcases p45741_3 (m.d 1 3) (by simp) with h45774 | h45774
                                      · rcases p45741_3 (m.d 1 4) (by simp) with h45775 | h45775
                                        · rcases p45741_3 (m.d 1 5) (by simp) with h45776 | h45776
                                          · linarith only [h45734, h45776, hlam]
                                          · linarith only [h39227, h45776, hlam]
                                        · linarith only [h45775, hlam, p45741_0]
                                      · linarith only [h33187, h45774, hlam]
                                    · linarith only [h0, h45773, hlam]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h45730, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h45732, hlam, p45741_1]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h41027, h45424, h45733, h45737, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45741_1]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  rcases p45741_3 (m.d 0 1) (by simp) with h45786 | h45786
                                  · linarith only [h45786, hlam, p45741_0]
                                  · rcases p45741_3 (m.d 1 2) (by simp) with h45788 | h45788
                                    · rcases p45741_3 (m.d 1 3) (by simp) with h45789 | h45789
                                      · rcases p45741_3 (m.d 1 4) (by simp) with h45790 | h45790
                                        · rcases p45741_3 (m.d 1 5) (by simp) with h45791 | h45791
                                          · rcases h1emax with h45792 | h45792 | h45792 | h45792 | h45792
                                            · rcases h2bigk with h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c | h45793c
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h0, hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45424, h45735, h45739, hc23, hc34, hlam, hphi, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41028, hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45424, hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                rcases p45793_3 (m.d 0 2) (by simp) with h45799 | h45799
                                                · linarith only [h0, h45799, hlam]
                                                · rcases p45793_3 (m.d 1 2) (by simp) with h45801 | h45801
                                                  · rcases p45793_3 (m.d 2 3) (by simp) with h45802 | h45802
                                                    · linarith only [h45729, h45802, hlam]
                                                    · rcases p45793_3 (m.d 2 4) (by simp) with h45804 | h45804
                                                      · linarith only [h45730, h45804, hlam]
                                                      · linarith only [h41028, h45804, hlam]
                                                  · linarith only [h0, h45801, hlam]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41027, h45424, h45729, h45732, h45735, h45739, hlam, p45793_2]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41027, h45424, h45739, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41027, h45424, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41027, hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45729, hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45735, hlam, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45737, hlam, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41027, h45730, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45730, hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                rcases p45793_3 (m.d 0 2) (by simp) with h45819 | h45819
                                                · linarith only [h41028, h45819, hlam]
                                                · linarith only [h41027, h45819, hlam]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41027, h45424, h45729, h45732, h45735, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h41027, h45731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45731, hlam, p45793_0]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                rcases p45793_3 (m.d 0 2) (by simp) with h45826 | h45826
                                                · linarith only [h45424, h45826, hlam]
                                                · linarith only [h41027, h45826, hlam]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [h45739, hlam, p45793_1]
                                              · have p45793_0 := h45793c.1
                                                have p45793_1 := h45793c.2.1
                                                have p45793_2 := h45793c.2.2.1
                                                have p45793_3 := h45793c.2.2.2
                                                linarith only [hlam, p45793_0]
                                            · linarith only [h0, h45792, hc01, hlam]
                                            · linarith only [h41027, h45424, h45732, h45737, h45740, h45792, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                            · linarith only [h45734, h45792, hc01, hlam, p45741_1]
                                            · linarith only [h45792, hc01, hlam, p45741_1]
                                          · linarith only [h45791, hlam, p45741_0]
                                        · linarith only [h36828, h45790, hlam]
                                      · linarith only [h33187, h45789, hlam]
                                    · linarith only [h0, h45788, hlam]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h45731, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h45733, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [h45734, hlam, p45741_0]
                                · have p45741_0 := h45741c.1
                                  have p45741_1 := h45741c.2.1
                                  have p45741_2 := h45741c.2.2.1
                                  have p45741_3 := h45741c.2.2.2
                                  linarith only [hlam, p45741_0]
                              · linarith only [h33187, h36828, h45724, h45728, h45740, hc01, hc14, hlam, hphi]
                            · linarith only [h41028, h45728, h45739, hlam]
                      · linarith only [h36828, h41028, h45728, h45734, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h41027, h41028, h45724, h45732, h45733, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45847 | h45847
                    · linarith only [h45726, h45732, h45847, hc03, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45849 | h45849
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45850 | h45850
                        · linarith only [h41027, h41028, h45730, h45732, h45850, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45852 | h45852
                          · linarith only [h41027, h45424, h45731, h45847, h45852, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45854 | h45854
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45855 | h45855
                              · rcases h1bigk with h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c | h45856c
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h0, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h33187, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h36828, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h39227, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  rcases p45856_3 (m.d 0 1) (by simp) with h45862 | h45862
                                  · linarith only [h45862, hlam, p45856_0]
                                  · rcases p45856_3 (m.d 1 2) (by simp) with h45864 | h45864
                                    · rcases p45856_3 (m.d 1 3) (by simp) with h45865 | h45865
                                      · linarith only [h45729, h45865, hlam]
                                      · linarith only [h33187, h45865, hlam]
                                    · linarith only [h45864, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h33187, hc01, hc12, hlam, hphi, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h41027, h45424, h45731, h45849, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h41027, h45424, h45731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h45732, hc01, hc34, hlam, hphi, ht12, ht23, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h45729, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h45732, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h45847, hlam, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  rcases p45856_3 (m.d 0 1) (by simp) with h45878 | h45878
                                  · linarith only [h45878, hlam, p45856_0]
                                  · rcases p45856_3 (m.d 1 2) (by simp) with h45880 | h45880
                                    · rcases p45856_3 (m.d 1 3) (by simp) with h45881 | h45881
                                      · linarith only [h45732, h45881, hlam]
                                      · linarith only [h33187, h45881, hlam]
                                    · linarith only [h0, h45880, hlam]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h45730, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h33187, hc01, hc14, hlam, hphi, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h41027, h45424, h45731, h45732, hc23, hc34, hlam, hphi, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  rcases p45856_3 (m.d 0 1) (by simp) with h45889 | h45889
                                  · linarith only [h45889, hlam, p45856_0]
                                  · rcases p45856_3 (m.d 1 2) (by simp) with h45891 | h45891
                                    · rcases p45856_3 (m.d 1 3) (by simp) with h45892 | h45892
                                      · linarith only [h45847, h45892, hlam]
                                      · linarith only [h33187, h45892, hlam]
                                    · linarith only [h0, h45891, hlam]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h45731, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h33187, hc01, hc15, hlam, hphi, p45856_1]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [h45849, hlam, p45856_0]
                                · have p45856_0 := h45856c.1
                                  have p45856_1 := h45856c.2.1
                                  have p45856_2 := h45856c.2.2.1
                                  have p45856_3 := h45856c.2.2.2
                                  linarith only [hlam, p45856_0]
                              · linarith only [h36828, h45728, h45732, h45855, hlam]
                            · linarith only [h41028, h45728, h45854, hlam]
                      · linarith only [h41028, h45728, h45730, h45849, hlam]
                · linarith only [h41027, h41028, h45730, h45731, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45904 | h45904
                · linarith only [h41027, h45424, h45730, h45904, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45906 | h45906
                  · linarith only [h33187, h45724, h45729, h45730, h45906, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45908 | h45908
                    · linarith only [h33187, h45726, h45906, h45908, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45910 | h45910
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45911 | h45911
                        · linarith only [h0, h41027, h45730, h45906, h45911, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45913 | h45913
                          · linarith only [h33187, h41027, h45908, h45913, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45915 | h45915
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45916 | h45916
                              · rcases h1bigk with h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c | h45917c
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h0, hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h33187, hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h36828, hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h39227, hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45904, h45911, h45915, hc01, hc34, hlam, hphi, ht12, ht23, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h33187, h45904, h45911, h45915, hc01, hc34, hlam, hphi, ht12, ht23, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45730, hlam, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45904, hlam, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45729, h45904, h45911, h45915, hc01, hc34, hlam, hphi, ht12, ht23, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45729, hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45906, hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45908, hlam, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  rcases p45917_3 (m.d 0 1) (by simp) with h45933 | h45933
                                  · linarith only [h45933, hlam, p45917_0]
                                  · rcases p45917_3 (m.d 1 2) (by simp) with h45935 | h45935
                                    · linarith only [h45730, h45935, hlam]
                                    · linarith only [h0, h45935, hlam]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h0, h45730, h45911, hc01, hc34, hlam, hphi, ht12, ht23, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h33187, h45730, h45911, hc01, hc34, hlam, hphi, ht12, ht23, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h39227, h45730, h45911, hc01, hc34, hlam, hphi, ht12, ht23, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  rcases p45917_3 (m.d 0 1) (by simp) with h45942 | h45942
                                  · linarith only [h45942, hlam, p45917_0]
                                  · rcases p45917_3 (m.d 1 2) (by simp) with h45944 | h45944
                                    · linarith only [h45904, h45944, hlam]
                                    · linarith only [h0, h45944, hlam]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h33187, h45729, hc01, hc15, hlam, hphi, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h33187, h45904, h45911, h45915, hc01, hc34, hlam, hphi, ht12, ht23, p45917_1]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [h45910, hlam, p45917_0]
                                · have p45917_0 := h45917c.1
                                  have p45917_1 := h45917c.2.1
                                  have p45917_2 := h45917c.2.2.1
                                  have p45917_3 := h45917c.2.2.2
                                  linarith only [hlam, p45917_0]
                              · linarith only [h36828, h45728, h45730, h45911, h45916, hlam]
                            · linarith only [h36828, h45728, h45730, h45915, hlam]
                      · linarith only [h36828, h45728, h45910, hlam]
            · linarith only [h0, h41027, h45729, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h45955 | h45955
            · rcases m.htr 1 2 4 (by decide) (by decide) with h45956 | h45956
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45957 | h45957
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45958 | h45958
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45959 | h45959
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45960 | h45960
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45961 | h45961
                        · linarith only [h33187, h41027, h41028, h45724, h45728, h45958, h45960, h45961, hc01, hc13, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45963 | h45963
                          · linarith only [h41027, h41028, h45728, h45955, h45958, h45960, h45963, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45965 | h45965
                            · linarith only [h41027, h41028, h45728, h45961, h45965, hc23, hc34, hlam, hphi]
                            · linarith only [h41027, h41028, h45955, h45958, h45960, h45965, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h41027, h41028, h45956, h45960, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h33187, h45724, h45958, h45959, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45970 | h45970
                    · linarith only [h33187, h45726, h45958, h45970, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45972 | h45972
                      · linarith only [h41027, h41028, h45728, h45958, h45972, hc23, hc34, hlam, hphi]
                      · linarith only [h41027, h41028, h45956, h45972, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h41027, h41028, h45956, h45957, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45976 | h45976
                · linarith only [h41027, h45424, h45956, h45976, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45978 | h45978
                  · linarith only [h33187, h45724, h45955, h45956, h45978, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45980 | h45980
                    · linarith only [h33187, h45726, h45978, h45980, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h45982 | h45982
                      · linarith only [h41027, h41028, h45728, h45978, h45982, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45984 | h45984
                        · linarith only [h36828, h41027, h41028, h45982, h45984, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h45986 | h45986
                          · linarith only [h33187, h36828, h41027, h41028, h45726, h45982, h45986, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45988 | h45988
                            · linarith only [h0, h45956, h45982, h45984, h45988, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h41027, h41028, h45988, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h41027, h41028, h45955, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 13704000 in
set_option maxHeartbeats 13704000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s40 m hb1 hb2 hb4 hb5 h0 h33187 h36828 h39227 h41027

end R2N4
