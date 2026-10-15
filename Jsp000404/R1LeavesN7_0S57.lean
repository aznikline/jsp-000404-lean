import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 0 1) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 0 1) ∧ (m.d 1 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 3) ≤ z)))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h20358 | h20358
  · rcases p20349_3 (m.d 1 2) (by simp) with h20359 | h20359
    · linarith only [h0, h20359, hlam]
    · rcases p20349_3 (m.d 1 3) (by simp) with h20361 | h20361
      · linarith only [h20361, hlam, p20349_0]
      · rcases p20349_3 (m.d 1 4) (by simp) with h20363 | h20363
        · linarith only [h2, h20363, hlam]
        · rcases p20349_3 (m.d 1 5) (by simp) with h20365 | h20365
          · linarith only [h20365, h3, hlam]
          · rcases h1emax with h20367 | h20367 | h20367 | h20367 | h20367
            · linarith only [h20335, h20367, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p20349_1]
            · rcases h2bigk with h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c | h20369c
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20338, h20343, h20345, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20369_1]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h4, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                rcases p20369_3 (m.d 0 2) (by simp) with h20373 | h20373
                · rcases p20369_3 (m.d 1 2) (by simp) with h20374 | h20374
                  · linarith only [h0, h20374, hlam]
                  · linarith only [h20337, h20374, hlam]
                · linarith only [h20373, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                rcases p20369_3 (m.d 0 2) (by simp) with h20378 | h20378
                · rcases p20369_3 (m.d 1 2) (by simp) with h20379 | h20379
                  · linarith only [h0, h20379, hlam]
                  · linarith only [h20338, h20379, hlam]
                · linarith only [h20378, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h0, hlam, p20369_1]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20335, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20335, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20369_1]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20335, h20343, h20345, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20369_1]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                rcases p20369_3 (m.d 0 2) (by simp) with h20388 | h20388
                · linarith only [h20388, hlam, p20369_0]
                · rcases p20369_3 (m.d 1 2) (by simp) with h20390 | h20390
                  · linarith only [h20335, h20390, hlam]
                  · rcases p20369_3 (m.d 2 3) (by simp) with h20392 | h20392
                    · rcases p20369_3 (m.d 2 4) (by simp) with h20393 | h20393
                      · linarith only [h20343, h20393, hlam]
                      · rcases p20369_3 (m.d 2 5) (by simp) with h20395 | h20395
                        · linarith only [h20344, h20395, hlam]
                        · rcases h4bigk with h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c | h20397c
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19748, h20337, h20343, hc34, hc45, hlam, hphi, p20397_1]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19744, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20369_1, p20397_1]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19745, h19748, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20369_1, p20397_1]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19748, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h2, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19745, h19748, h2, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20369_1, p20397_1]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19745, h19748, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20369_1, p20397_1]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h20341, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19744, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h20337, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19744, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20369_1, p20397_1]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h20345, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h19746, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h20339, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h20343, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [h20347, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            rcases p20397_3 (m.d 0 4) (by simp) with h20418 | h20418
                            · linarith only [h20418, hlam, p20397_0]
                            · rcases p20397_3 (m.d 1 4) (by simp) with h20420 | h20420
                              · linarith only [h20341, h20420, hlam]
                              · rcases p20397_3 (m.d 2 4) (by simp) with h20422 | h20422
                                · linarith only [h20345, h20422, hlam]
                                · rcases p20397_3 (m.d 3 4) (by simp) with h20424 | h20424
                                  · linarith only [h20347, h20424, hlam]
                                  · rcases p20397_3 (m.d 4 5) (by simp) with h20426 | h20426
                                    · rcases h5bigk with h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c | h20427c
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19745, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p20369_1, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19745, h20345, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20369_1, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19745, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p20369_1, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19748, hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h3, hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20345, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19745, h3, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p20369_1, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20341, hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19745, hlam, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20338, hlam, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19745, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p20369_1, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20345, hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19747, hlam, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20340, hlam, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20344, hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20347, hlam, p20427_0]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h19748, hc04, hc45, hlam, hphi, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20337, h20341, h20343, hc34, hc45, hlam, hphi, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20343, h20345, hc34, hc45, hlam, hphi, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [h20347, hc34, hc45, hlam, hphi, p20427_1]
                                      · have p20427_0 := h20427c.1
                                        have p20427_1 := h20427c.2.1
                                        have p20427_2 := h20427c.2.2.1
                                        have p20427_3 := h20427c.2.2.2
                                        linarith only [hlam, p20427_0]
                                    · linarith only [h20426, hlam, p20397_0]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            rcases p20397_3 (m.d 0 4) (by simp) with h20454 | h20454
                            · linarith only [h19748, h20454, hlam]
                            · linarith only [h2, h20454, hlam]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            rcases p20397_3 (m.d 0 4) (by simp) with h20457 | h20457
                            · linarith only [h19748, h20457, hlam]
                            · linarith only [h19744, h20457, hlam]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            rcases p20397_3 (m.d 0 4) (by simp) with h20460 | h20460
                            · linarith only [h19748, h20460, hlam]
                            · linarith only [h19746, h20460, hlam]
                          · have p20397_0 := h20397c.1
                            have p20397_1 := h20397c.2.1
                            have p20397_2 := h20397c.2.2.1
                            have p20397_3 := h20397c.2.2.2
                            linarith only [hlam, p20397_0]
                    · linarith only [h20392, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                rcases p20369_3 (m.d 0 2) (by simp) with h20465 | h20465
                · linarith only [h20465, h4, hlam]
                · linarith only [h0, h20465, hlam]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                rcases p20369_3 (m.d 0 2) (by simp) with h20469 | h20469
                · linarith only [h20469, h4, hlam]
                · linarith only [h19744, h20469, hlam]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                rcases p20369_3 (m.d 0 2) (by simp) with h20472 | h20472
                · linarith only [h20472, h4, hlam]
                · linarith only [h19745, h20472, hlam]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h19744, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20337, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20343, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20345, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h19745, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20338, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h20344, hlam, p20369_0]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [h0, h20338, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20369_1]
              · have p20369_0 := h20369c.1
                have p20369_1 := h20369c.2.1
                have p20369_2 := h20369c.2.2.1
                have p20369_3 := h20369c.2.2.2
                linarith only [hlam, p20369_0]
            · rcases h2bigk with h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c | h20485c
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h4, hc12, hc23, hlam, hphi, p20485_1]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h4, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                rcases p20485_3 (m.d 0 2) (by simp) with h20489 | h20489
                · rcases p20485_3 (m.d 1 2) (by simp) with h20490 | h20490
                  · linarith only [h0, h20490, hlam]
                  · linarith only [h20337, h20490, hlam]
                · linarith only [h20489, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                rcases p20485_3 (m.d 0 2) (by simp) with h20494 | h20494
                · rcases p20485_3 (m.d 1 2) (by simp) with h20495 | h20495
                  · linarith only [h0, h20495, hlam]
                  · linarith only [h20338, h20495, hlam]
                · linarith only [h20494, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h0, hlam, p20485_1]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20335, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20335, h20343, h20367, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20485_1]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20335, h20344, h20347, h20367, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20485_1]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                rcases p20485_3 (m.d 0 2) (by simp) with h20504 | h20504
                · linarith only [h20504, hlam, p20485_0]
                · rcases p20485_3 (m.d 1 2) (by simp) with h20506 | h20506
                  · linarith only [h20335, h20506, hlam]
                  · rcases p20485_3 (m.d 2 3) (by simp) with h20508 | h20508
                    · rcases p20485_3 (m.d 2 4) (by simp) with h20509 | h20509
                      · linarith only [h20343, h20509, hlam]
                      · rcases p20485_3 (m.d 2 5) (by simp) with h20511 | h20511
                        · linarith only [h20344, h20511, hlam]
                        · rcases h4bigk with h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c | h20513c
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19744, h20337, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20513_1]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19744, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20513_1]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19745, h19748, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20513_1]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19748, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h2, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19745, h19748, h2, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20513_1]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19745, h19748, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20513_1]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h20341, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19744, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h20337, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19744, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20513_1]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h20345, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h19746, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h20339, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h20343, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [h20347, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            rcases p20513_3 (m.d 0 4) (by simp) with h20534 | h20534
                            · linarith only [h20534, hlam, p20513_0]
                            · rcases p20513_3 (m.d 1 4) (by simp) with h20536 | h20536
                              · linarith only [h20341, h20536, hlam]
                              · rcases p20513_3 (m.d 2 4) (by simp) with h20538 | h20538
                                · linarith only [h20345, h20538, hlam]
                                · rcases p20513_3 (m.d 3 4) (by simp) with h20540 | h20540
                                  · linarith only [h20347, h20540, hlam]
                                  · rcases p20513_3 (m.d 4 5) (by simp) with h20542 | h20542
                                    · rcases h5bigk with h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c | h20543c
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19745, h20341, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19745, h20345, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19745, h20347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19748, hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h3, hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20345, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19745, h20347, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20341, hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19745, hlam, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20338, hlam, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19745, h20347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20485_1, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20345, hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19747, hlam, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20340, hlam, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20344, hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20347, hlam, p20543_0]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h19747, h20347, hc34, hc45, hlam, hphi, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20340, h20347, hc34, hc45, hlam, hphi, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20344, h20347, hc34, hc45, hlam, hphi, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [h20347, hc34, hc45, hlam, hphi, p20543_1]
                                      · have p20543_0 := h20543c.1
                                        have p20543_1 := h20543c.2.1
                                        have p20543_2 := h20543c.2.2.1
                                        have p20543_3 := h20543c.2.2.2
                                        linarith only [hlam, p20543_0]
                                    · linarith only [h20542, hlam, p20513_0]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            rcases p20513_3 (m.d 0 4) (by simp) with h20570 | h20570
                            · linarith only [h19748, h20570, hlam]
                            · linarith only [h2, h20570, hlam]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            rcases p20513_3 (m.d 0 4) (by simp) with h20573 | h20573
                            · linarith only [h19748, h20573, hlam]
                            · linarith only [h19744, h20573, hlam]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            rcases p20513_3 (m.d 0 4) (by simp) with h20576 | h20576
                            · linarith only [h19748, h20576, hlam]
                            · linarith only [h19746, h20576, hlam]
                          · have p20513_0 := h20513c.1
                            have p20513_1 := h20513c.2.1
                            have p20513_2 := h20513c.2.2.1
                            have p20513_3 := h20513c.2.2.2
                            linarith only [hlam, p20513_0]
                    · linarith only [h20508, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                rcases p20485_3 (m.d 0 2) (by simp) with h20581 | h20581
                · linarith only [h20581, h4, hlam]
                · linarith only [h0, h20581, hlam]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                rcases p20485_3 (m.d 0 2) (by simp) with h20585 | h20585
                · linarith only [h20585, h4, hlam]
                · linarith only [h19744, h20585, hlam]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                rcases p20485_3 (m.d 0 2) (by simp) with h20588 | h20588
                · linarith only [h20588, h4, hlam]
                · linarith only [h19745, h20588, hlam]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h19744, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20337, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20343, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20345, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h19745, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20338, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h20344, hlam, p20485_0]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [h0, h20338, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20485_1]
              · have p20485_0 := h20485c.1
                have p20485_1 := h20485c.2.1
                have p20485_2 := h20485c.2.2.1
                have p20485_3 := h20485c.2.2.2
                linarith only [hlam, p20485_0]
            · rcases h2bigk with h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c | h20601c
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h4, hc12, hc23, hlam, hphi, p20601_1]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h4, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                rcases p20601_3 (m.d 0 2) (by simp) with h20605 | h20605
                · rcases p20601_3 (m.d 1 2) (by simp) with h20606 | h20606
                  · linarith only [h0, h20606, hlam]
                  · linarith only [h20337, h20606, hlam]
                · linarith only [h20605, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                rcases p20601_3 (m.d 0 2) (by simp) with h20610 | h20610
                · rcases p20601_3 (m.d 1 2) (by simp) with h20611 | h20611
                  · linarith only [h0, h20611, hlam]
                  · linarith only [h20338, h20611, hlam]
                · linarith only [h20610, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h0, hlam, p20601_1]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20335, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20335, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20601_1]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20335, h20344, h20347, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20601_1]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                rcases p20601_3 (m.d 0 2) (by simp) with h20620 | h20620
                · linarith only [h20620, hlam, p20601_0]
                · rcases p20601_3 (m.d 1 2) (by simp) with h20622 | h20622
                  · linarith only [h20335, h20622, hlam]
                  · rcases p20601_3 (m.d 2 3) (by simp) with h20624 | h20624
                    · rcases p20601_3 (m.d 2 4) (by simp) with h20625 | h20625
                      · linarith only [h20343, h20625, hlam]
                      · rcases p20601_3 (m.d 2 5) (by simp) with h20627 | h20627
                        · linarith only [h20344, h20627, hlam]
                        · rcases h4bigk with h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c | h20629c
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19744, h20337, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20629_1]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19744, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20629_1]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19745, h19748, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20629_1]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19748, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h2, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19745, h19748, h2, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20629_1]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19745, h19748, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20629_1]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h20341, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19744, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h20337, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19744, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20629_1]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h20345, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h19746, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h20339, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h20343, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [h20347, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            rcases p20629_3 (m.d 0 4) (by simp) with h20650 | h20650
                            · linarith only [h20650, hlam, p20629_0]
                            · rcases p20629_3 (m.d 1 4) (by simp) with h20652 | h20652
                              · linarith only [h20341, h20652, hlam]
                              · rcases p20629_3 (m.d 2 4) (by simp) with h20654 | h20654
                                · linarith only [h20345, h20654, hlam]
                                · rcases p20629_3 (m.d 3 4) (by simp) with h20656 | h20656
                                  · linarith only [h20347, h20656, hlam]
                                  · rcases p20629_3 (m.d 4 5) (by simp) with h20658 | h20658
                                    · rcases h5bigk with h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c | h20659c
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19745, h20341, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19745, h20344, h20347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19745, h20347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19748, hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h3, hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20344, h20347, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19745, h20347, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20341, hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19745, hlam, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20338, hlam, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19745, h20347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20601_1, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20345, hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19747, hlam, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20340, hlam, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20344, hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20347, hlam, p20659_0]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h19747, h20347, hc34, hc45, hlam, hphi, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20340, h20347, hc34, hc45, hlam, hphi, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20344, h20347, hc34, hc45, hlam, hphi, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [h20347, hc34, hc45, hlam, hphi, p20659_1]
                                      · have p20659_0 := h20659c.1
                                        have p20659_1 := h20659c.2.1
                                        have p20659_2 := h20659c.2.2.1
                                        have p20659_3 := h20659c.2.2.2
                                        linarith only [hlam, p20659_0]
                                    · linarith only [h20658, hlam, p20629_0]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            rcases p20629_3 (m.d 0 4) (by simp) with h20686 | h20686
                            · linarith only [h19748, h20686, hlam]
                            · linarith only [h2, h20686, hlam]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            rcases p20629_3 (m.d 0 4) (by simp) with h20689 | h20689
                            · linarith only [h19748, h20689, hlam]
                            · linarith only [h19744, h20689, hlam]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            rcases p20629_3 (m.d 0 4) (by simp) with h20692 | h20692
                            · linarith only [h19748, h20692, hlam]
                            · linarith only [h19746, h20692, hlam]
                          · have p20629_0 := h20629c.1
                            have p20629_1 := h20629c.2.1
                            have p20629_2 := h20629c.2.2.1
                            have p20629_3 := h20629c.2.2.2
                            linarith only [hlam, p20629_0]
                    · linarith only [h20624, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                rcases p20601_3 (m.d 0 2) (by simp) with h20697 | h20697
                · linarith only [h20697, h4, hlam]
                · linarith only [h0, h20697, hlam]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                rcases p20601_3 (m.d 0 2) (by simp) with h20701 | h20701
                · linarith only [h20701, h4, hlam]
                · linarith only [h19744, h20701, hlam]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                rcases p20601_3 (m.d 0 2) (by simp) with h20704 | h20704
                · linarith only [h20704, h4, hlam]
                · linarith only [h19745, h20704, hlam]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h19744, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20337, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20343, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20345, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h19745, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20338, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h20344, hlam, p20601_0]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [h0, h20338, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20601_1]
              · have p20601_0 := h20601c.1
                have p20601_1 := h20601c.2.1
                have p20601_2 := h20601c.2.2.1
                have p20601_3 := h20601c.2.2.2
                linarith only [hlam, p20601_0]
            · rcases h2bigk with h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c | h20717c
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h4, hc12, hc23, hlam, hphi, p20717_1]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h4, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                rcases p20717_3 (m.d 0 2) (by simp) with h20721 | h20721
                · rcases p20717_3 (m.d 1 2) (by simp) with h20722 | h20722
                  · linarith only [h0, h20722, hlam]
                  · linarith only [h20337, h20722, hlam]
                · linarith only [h20721, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                rcases p20717_3 (m.d 0 2) (by simp) with h20726 | h20726
                · rcases p20717_3 (m.d 1 2) (by simp) with h20727 | h20727
                  · linarith only [h0, h20727, hlam]
                  · linarith only [h20338, h20727, hlam]
                · linarith only [h20726, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h0, hlam, p20717_1]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20335, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20335, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20717_1]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20335, h20344, h20347, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20349_1, p20717_1]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                rcases p20717_3 (m.d 0 2) (by simp) with h20736 | h20736
                · linarith only [h20736, hlam, p20717_0]
                · rcases p20717_3 (m.d 1 2) (by simp) with h20738 | h20738
                  · linarith only [h20335, h20738, hlam]
                  · rcases p20717_3 (m.d 2 3) (by simp) with h20740 | h20740
                    · rcases p20717_3 (m.d 2 4) (by simp) with h20741 | h20741
                      · linarith only [h20343, h20741, hlam]
                      · rcases p20717_3 (m.d 2 5) (by simp) with h20743 | h20743
                        · linarith only [h20344, h20743, hlam]
                        · rcases h4bigk with h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c | h20745c
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19744, h20337, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20745_1]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19744, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20745_1]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19745, h19748, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20745_1]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19748, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h2, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19745, h19748, h2, h20343, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20745_1]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19745, h19748, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20745_1]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h20341, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19744, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h20337, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19744, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20745_1]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h20345, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h19746, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h20339, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h20343, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [h20347, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            rcases p20745_3 (m.d 0 4) (by simp) with h20766 | h20766
                            · linarith only [h20766, hlam, p20745_0]
                            · rcases p20745_3 (m.d 1 4) (by simp) with h20768 | h20768
                              · linarith only [h20341, h20768, hlam]
                              · rcases p20745_3 (m.d 2 4) (by simp) with h20770 | h20770
                                · linarith only [h20345, h20770, hlam]
                                · rcases p20745_3 (m.d 3 4) (by simp) with h20772 | h20772
                                  · linarith only [h20347, h20772, hlam]
                                  · rcases p20745_3 (m.d 4 5) (by simp) with h20774 | h20774
                                    · rcases h5bigk with h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c | h20775c
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19745, h20341, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19745, h20345, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19745, h20347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19748, hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h3, hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20345, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19745, h20347, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20341, hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19745, hlam, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20338, hlam, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19745, h20347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20717_1, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20345, hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19747, hlam, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20340, hlam, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20344, hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20347, hlam, p20775_0]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h19747, h20347, hc34, hc45, hlam, hphi, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20340, h20347, hc34, hc45, hlam, hphi, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20344, h20347, hc34, hc45, hlam, hphi, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [h20347, hc34, hc45, hlam, hphi, p20775_1]
                                      · have p20775_0 := h20775c.1
                                        have p20775_1 := h20775c.2.1
                                        have p20775_2 := h20775c.2.2.1
                                        have p20775_3 := h20775c.2.2.2
                                        linarith only [hlam, p20775_0]
                                    · linarith only [h20774, hlam, p20745_0]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            rcases p20745_3 (m.d 0 4) (by simp) with h20802 | h20802
                            · linarith only [h19748, h20802, hlam]
                            · linarith only [h2, h20802, hlam]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            rcases p20745_3 (m.d 0 4) (by simp) with h20805 | h20805
                            · linarith only [h19748, h20805, hlam]
                            · linarith only [h19744, h20805, hlam]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            rcases p20745_3 (m.d 0 4) (by simp) with h20808 | h20808
                            · linarith only [h19748, h20808, hlam]
                            · linarith only [h19746, h20808, hlam]
                          · have p20745_0 := h20745c.1
                            have p20745_1 := h20745c.2.1
                            have p20745_2 := h20745c.2.2.1
                            have p20745_3 := h20745c.2.2.2
                            linarith only [hlam, p20745_0]
                    · linarith only [h20740, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                rcases p20717_3 (m.d 0 2) (by simp) with h20813 | h20813
                · linarith only [h20813, h4, hlam]
                · linarith only [h0, h20813, hlam]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                rcases p20717_3 (m.d 0 2) (by simp) with h20817 | h20817
                · linarith only [h20817, h4, hlam]
                · linarith only [h19744, h20817, hlam]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                rcases p20717_3 (m.d 0 2) (by simp) with h20820 | h20820
                · linarith only [h20820, h4, hlam]
                · linarith only [h19745, h20820, hlam]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h19744, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20337, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20343, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20345, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h19745, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20338, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h20344, hlam, p20717_0]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [h0, h20338, h20343, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20717_1]
              · have p20717_0 := h20717c.1
                have p20717_1 := h20717c.2.1
                have p20717_2 := h20717c.2.2.1
                have p20717_3 := h20717c.2.2.2
                linarith only [hlam, p20717_0]
  · linarith only [h20358, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 0 1) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 0 1) ∧ (m.d 1 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 4) ≤ z)))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h20834 | h20834
  · rcases p20349_3 (m.d 1 2) (by simp) with h20835 | h20835
    · linarith only [h0, h20835, hlam]
    · linarith only [h20337, h20835, hlam]
  · linarith only [h20834, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h20839 | h20839
  · rcases p20349_3 (m.d 1 2) (by simp) with h20840 | h20840
    · linarith only [h0, h20840, hlam]
    · linarith only [h20338, h20840, hlam]
  · linarith only [h20839, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h0, hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [hlam, p20349_0]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  linarith only [h20335, hlam, p20349_1]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0_x0_x1_x1_x8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19746 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19747 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19748 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h20335 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h20337 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20338 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20339 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20340 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20341 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h20343 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h20344 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h20345 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h20347 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h20349c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have p20349_0 := h20349c.1
  have p20349_1 := h20349c.2.1
  have p20349_2 := h20349c.2.2.1
  have p20349_3 := h20349c.2.2.2
  rcases p20349_3 (m.d 0 1) (by simp) with h20847 | h20847
  · rcases p20349_3 (m.d 1 2) (by simp) with h20848 | h20848
    · rcases p20349_3 (m.d 1 3) (by simp) with h20849 | h20849
      · rcases p20349_3 (m.d 1 4) (by simp) with h20850 | h20850
        · linarith only [h20337, h20850, hlam]
        · rcases p20349_3 (m.d 1 5) (by simp) with h20852 | h20852
          · linarith only [h20338, h20852, hlam]
          · linarith only [h20341, h20852, hlam]
      · linarith only [h20339, h20849, hlam]
    · linarith only [h20337, h20848, hlam]
  · linarith only [h2, h20847, hlam]

end R2N4
