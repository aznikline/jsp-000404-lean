import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S4
import Jsp000404.R1LeavesN7_16S5
import Jsp000404.R1LeavesN7_16S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3093 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3422 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3633 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h4387 | h4387
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4388 | h4388
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4389 | h4389
      · linarith only [h0, h4, h4389, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4391 | h4391
        · linarith only [h0, h3093, h4391, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4393 | h4393
          · linarith only [h0, h3422, h4393, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4395 | h4395
            · linarith only [h1, h3633, h4387, h4395, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4397 | h4397
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4398 | h4398
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4399 | h4399
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4400 | h4400
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4401 | h4401
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4402 | h4402
                        · rcases h1bigk with h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c | h4403c
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            rcases p4403_3 (m.d 0 1) (by simp) with h4405 | h4405
                            · rcases p4403_3 (m.d 1 2) (by simp) with h4406 | h4406
                              · linarith only [h4406, hlam, p4403_0]
                              · rcases p4403_3 (m.d 1 3) (by simp) with h4408 | h4408
                                · linarith only [h1, h4408, hlam]
                                · linarith only [h4389, h4408, hlam]
                            · linarith only [h4405, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4397, h4402, hc01, hc45, hlam, hphi, ht0b, ht5b, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4395, h4397, h4402, hc01, hc45, hlam, hphi, ht0b, ht5b, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            rcases p4403_3 (m.d 0 1) (by simp) with h4414 | h4414
                            · rcases p4403_3 (m.d 1 2) (by simp) with h4415 | h4415
                              · linarith only [h0, h4415, hlam]
                              · rcases p4403_3 (m.d 1 3) (by simp) with h4417 | h4417
                                · linarith only [h1, h4417, hlam]
                                · linarith only [h4397, h4417, hlam]
                            · linarith only [h4414, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h0, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4389, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4391, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4393, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h1, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4395, hlam, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h1, h3633, h4393, h4399, hc12, hc23, hlam, hphi, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h2, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h2, h3633, h4399, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h2, h3633, h4393, h4399, hc12, hc23, hlam, hphi, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h3, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4403_1]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4397, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [h4398, hlam, p4403_0]
                          · have p4403_0 := h4403c.1
                            have p4403_1 := h4403c.2.1
                            have p4403_2 := h4403c.2.2.1
                            have p4403_3 := h4403c.2.2.2
                            linarith only [hlam, p4403_0]
                        · linarith only [h3633, h4388, h4402, hlam]
                      · linarith only [h0, h3, h3093, h3633, h4387, h4398, h4399, h4401, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h3633, h4397, h4400, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4444 | h4444
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4445 | h4445
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4446 | h4446
                        · rcases h1bigk with h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c | h4447c
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            rcases p4447_3 (m.d 0 1) (by simp) with h4449 | h4449
                            · rcases p4447_3 (m.d 1 2) (by simp) with h4450 | h4450
                              · linarith only [h4450, hlam, p4447_0]
                              · rcases p4447_3 (m.d 1 3) (by simp) with h4452 | h4452
                                · linarith only [h1, h4452, hlam]
                                · linarith only [h4389, h4452, hlam]
                            · linarith only [h4449, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4397, hc01, hc35, hlam, hphi, ht0b, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4395, h4397, h4446, hc01, hc45, hlam, hphi, ht0b, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            rcases p4447_3 (m.d 0 1) (by simp) with h4458 | h4458
                            · rcases p4447_3 (m.d 1 2) (by simp) with h4459 | h4459
                              · linarith only [h0, h4459, hlam]
                              · rcases p4447_3 (m.d 1 3) (by simp) with h4461 | h4461
                                · linarith only [h1, h4461, hlam]
                                · linarith only [h4397, h4461, hlam]
                            · linarith only [h4458, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h0, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4389, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4391, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4393, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h1, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4395, hlam, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h1, h4, h4399, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h2, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h2, h4393, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h3, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4447_1]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4397, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [h4398, hlam, p4447_0]
                          · have p4447_0 := h4447c.1
                            have p4447_1 := h4447c.2.1
                            have p4447_2 := h4447c.2.2.1
                            have p4447_3 := h4447c.2.2.2
                            linarith only [hlam, p4447_0]
                        · linarith only [h3422, h4399, h4444, h4446, hc02, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h3, h3093, h3422, h4398, h4399, h4444, h4445, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h4387, h4444, hlam]
                · linarith only [h4395, h4397, h4398, hlam]
              · linarith only [h3633, h4387, h4397, hc13, hc34, hlam, hphi]
    · linarith only [h3633, h4387, h4388, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4491 | h4491
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4492 | h4492
      · linarith only [h0, h4, h4492, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4494 | h4494
        · linarith only [h0, h3093, h4494, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4496 | h4496
          · linarith only [h0, h3422, h4496, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4498 | h4498
            · linarith only [h1, h3633, h4498, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4500 | h4500
              · linarith only [h1, h4387, h4500, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4502 | h4502
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4503 | h4503
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4504 | h4504
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4505 | h4505
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4506 | h4506
                        · rcases h1bigk with h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c | h4507c
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            rcases p4507_3 (m.d 0 1) (by simp) with h4509 | h4509
                            · rcases p4507_3 (m.d 1 2) (by simp) with h4510 | h4510
                              · linarith only [h4510, hlam, p4507_0]
                              · rcases p4507_3 (m.d 1 3) (by simp) with h4512 | h4512
                                · linarith only [h1, h4512, hlam]
                                · linarith only [h4492, h4512, hlam]
                            · linarith only [h4509, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            rcases p4507_3 (m.d 0 1) (by simp) with h4516 | h4516
                            · rcases p4507_3 (m.d 1 2) (by simp) with h4517 | h4517
                              · linarith only [h0, h4517, hlam]
                              · rcases p4507_3 (m.d 1 3) (by simp) with h4519 | h4519
                                · linarith only [h4519, hlam, p4507_0]
                                · rcases p4507_3 (m.d 1 4) (by simp) with h4521 | h4521
                                  · linarith only [h2, h4521, hlam]
                                  · linarith only [h4498, h4521, hlam]
                            · linarith only [h4516, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h4502, hc01, hc45, hlam, hphi, ht0b, ht5b, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            rcases p4507_3 (m.d 0 1) (by simp) with h4526 | h4526
                            · rcases p4507_3 (m.d 1 2) (by simp) with h4527 | h4527
                              · linarith only [h0, h4527, hlam]
                              · rcases p4507_3 (m.d 1 3) (by simp) with h4529 | h4529
                                · linarith only [h1, h4529, hlam]
                                · rcases p4507_3 (m.d 1 4) (by simp) with h4531 | h4531
                                  · linarith only [h2, h4531, hlam]
                                  · linarith only [h4502, h4531, hlam]
                            · linarith only [h4526, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h0, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h4492, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h4494, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h4496, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h1, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h1, h4387, h4504, hc12, hc25, hlam, hphi, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h4498, hlam, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h4500, hlam, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h2, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h2, h4492, h4500, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h3, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h3, h4492, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4507_1]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [h4502, hlam, p4507_0]
                          · have p4507_0 := h4507c.1
                            have p4507_1 := h4507c.2.1
                            have p4507_2 := h4507c.2.2.1
                            have p4507_3 := h4507c.2.2.2
                            linarith only [hlam, p4507_0]
                        · linarith only [h3633, h4491, h4506, hlam]
                      · linarith only [h2, h3093, h3633, h4502, h4503, h4505, hc02, hc23, hlam, hphi]
                    · linarith only [h1, h3633, h4492, h4503, h4504, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4558 | h4558
                    · linarith only [h1, h4387, h4492, h4503, h4558, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4560 | h4560
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4561 | h4561
                        · rcases h1bigk with h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c | h4562c
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            rcases p4562_3 (m.d 0 1) (by simp) with h4564 | h4564
                            · rcases p4562_3 (m.d 1 2) (by simp) with h4565 | h4565
                              · linarith only [h4565, hlam, p4562_0]
                              · rcases p4562_3 (m.d 1 3) (by simp) with h4567 | h4567
                                · linarith only [h1, h4567, hlam]
                                · linarith only [h4492, h4567, hlam]
                            · linarith only [h4564, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            rcases p4562_3 (m.d 0 1) (by simp) with h4571 | h4571
                            · rcases p4562_3 (m.d 1 2) (by simp) with h4572 | h4572
                              · linarith only [h0, h4572, hlam]
                              · rcases p4562_3 (m.d 1 3) (by simp) with h4574 | h4574
                                · linarith only [h4574, hlam, p4562_0]
                                · rcases p4562_3 (m.d 1 4) (by simp) with h4576 | h4576
                                  · linarith only [h2, h4576, hlam]
                                  · linarith only [h4498, h4576, hlam]
                            · linarith only [h4571, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h4502, hc01, hc45, hlam, hphi, ht0b, ht5b, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            rcases p4562_3 (m.d 0 1) (by simp) with h4581 | h4581
                            · rcases p4562_3 (m.d 1 2) (by simp) with h4582 | h4582
                              · linarith only [h0, h4582, hlam]
                              · rcases p4562_3 (m.d 1 3) (by simp) with h4584 | h4584
                                · linarith only [h1, h4584, hlam]
                                · rcases p4562_3 (m.d 1 4) (by simp) with h4586 | h4586
                                  · linarith only [h2, h4586, hlam]
                                  · linarith only [h4502, h4586, hlam]
                            · linarith only [h4581, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h0, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h4492, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h4494, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h4496, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h1, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h4498, hlam, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h4500, hlam, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h2, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h2, hc01, hc15, hlam, hphi, ht0b, ht5b, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h3, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h3, h3093, h4491, h4492, h4503, hc12, hc34, hlam, hphi, ht23, p4562_1]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [h4502, hlam, p4562_0]
                          · have p4562_0 := h4562c.1
                            have p4562_1 := h4562c.2.1
                            have p4562_2 := h4562c.2.2.1
                            have p4562_3 := h4562c.2.2.2
                            linarith only [hlam, p4562_0]
                        · linarith only [h3093, h4491, h4503, h4561, hlam]
                      · linarith only [h2, h3093, h4502, h4560, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4612 | h4612
                  · linarith only [h3633, h4491, h4492, h4498, h4502, h4612, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4614 | h4614
                    · linarith only [h4387, h4612, h4614, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4616 | h4616
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4617 | h4617
                        · rcases h1bigk with h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c | h4618c
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            rcases p4618_3 (m.d 0 1) (by simp) with h4620 | h4620
                            · rcases p4618_3 (m.d 1 2) (by simp) with h4621 | h4621
                              · linarith only [h4621, hlam, p4618_0]
                              · rcases p4618_3 (m.d 1 3) (by simp) with h4623 | h4623
                                · linarith only [h1, h4623, hlam]
                                · linarith only [h4492, h4623, hlam]
                            · linarith only [h4620, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            rcases p4618_3 (m.d 0 1) (by simp) with h4627 | h4627
                            · rcases p4618_3 (m.d 1 2) (by simp) with h4628 | h4628
                              · linarith only [h0, h4628, hlam]
                              · rcases p4618_3 (m.d 1 3) (by simp) with h4630 | h4630
                                · linarith only [h4630, hlam, p4618_0]
                                · rcases p4618_3 (m.d 1 4) (by simp) with h4632 | h4632
                                  · linarith only [h2, h4632, hlam]
                                  · linarith only [h4498, h4632, hlam]
                            · linarith only [h4627, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            rcases p4618_3 (m.d 0 1) (by simp) with h4636 | h4636
                            · rcases p4618_3 (m.d 1 2) (by simp) with h4637 | h4637
                              · linarith only [h0, h4637, hlam]
                              · rcases p4618_3 (m.d 1 3) (by simp) with h4639 | h4639
                                · linarith only [h1, h4639, hlam]
                                · rcases p4618_3 (m.d 1 4) (by simp) with h4641 | h4641
                                  · linarith only [h4641, hlam, p4618_0]
                                  · rcases p4618_3 (m.d 1 5) (by simp) with h4643 | h4643
                                    · linarith only [h3, h4643, hlam]
                                    · linarith only [h4502, h4643, hlam]
                            · linarith only [h4636, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            rcases p4618_3 (m.d 0 1) (by simp) with h4647 | h4647
                            · rcases p4618_3 (m.d 1 2) (by simp) with h4648 | h4648
                              · linarith only [h0, h4648, hlam]
                              · rcases p4618_3 (m.d 1 3) (by simp) with h4650 | h4650
                                · linarith only [h1, h4650, hlam]
                                · rcases p4618_3 (m.d 1 4) (by simp) with h4652 | h4652
                                  · linarith only [h2, h4652, hlam]
                                  · rcases p4618_3 (m.d 1 5) (by simp) with h4654 | h4654
                                    · linarith only [h4654, hlam, p4618_0]
                                    · rcases h1emin with h4656 | h4656 | h4656 | h4656 | h4656
                                      · rcases h5bigk with h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          rcases p4657_3 (m.d 0 5) (by simp) with h4659 | h4659
                                          · rcases p4657_3 (m.d 1 5) (by simp) with h4660 | h4660
                                            · linarith only [h3, h4660, hlam]
                                            · rcases p4657_3 (m.d 2 5) (by simp) with h4662 | h4662
                                              · rcases p4657_3 (m.d 3 5) (by simp) with h4663 | h4663
                                                · rcases p4657_3 (m.d 4 5) (by simp) with h4664 | h4664
                                                  · linarith only [h4491, h4664, hlam]
                                                  · linarith only [h4502, h4664, hlam]
                                                · linarith only [h4500, h4663, hlam]
                                              · linarith only [h4496, h4662, hlam]
                                          · linarith only [h3, h4659, hlam]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h3422, hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4387, hlam, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h3093, h4491, h4492, h4498, h4502, hc12, hc24, hlam, hphi, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h3, hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4496, hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4500, hlam, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4502, hlam, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4491, h4492, h4498, h4502, hc12, hc25, hlam, hphi, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          rcases p4657_3 (m.d 0 5) (by simp) with h4679 | h4679
                                          · linarith only [h3422, h4679, hlam]
                                          · linarith only [h3, h4679, hlam]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4614, hlam, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4492, h4498, h4502, h4614, h4617, hc12, hc34, hlam, hphi, ht23, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4491, h4492, h4498, h4502, h4617, hc12, hc34, hlam, hphi, ht23, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          rcases p4657_3 (m.d 0 5) (by simp) with h4686 | h4686
                                          · linarith only [h4387, h4686, hlam]
                                          · linarith only [h3, h4686, hlam]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h0, h3422, h4617, hc12, hc34, hlam, hphi, ht23, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4492, h4498, h4502, h4617, hc12, hc34, hlam, hphi, ht23, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4491, hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h3093, h4491, h4496, h4612, hc12, hc34, hlam, hphi, ht23, p4657_1]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4616, hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [h4617, hlam, p4657_0]
                                        · have p4657_0 := h4657c.1
                                          have p4657_1 := h4657c.2.1
                                          have p4657_2 := h4657c.2.2.1
                                          have p4657_3 := h4657c.2.2.2
                                          linarith only [hlam, p4657_0]
                                      · linarith only [h4496, h4656, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4618_1]
                                      · linarith only [h1, h4, h4614, h4617, h4656, hc34, hlam, ht12, ht23]
                                      · linarith only [h3093, h4491, h4502, h4612, h4656, hc34, hlam, ht12, ht23]
                                      · linarith only [h4656, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4618_1]
                            · linarith only [h4647, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h0, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h4492, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h4494, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h4496, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h1, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h4498, hlam, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h4500, hlam, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h2, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h4502, hlam, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h3, hlam, p4618_0]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h3, h3093, h4491, h4492, h4612, hc12, hc34, hlam, hphi, ht23, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [h3093, h4491, h4502, h4612, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4618_1]
                          · have p4618_0 := h4618c.1
                            have p4618_1 := h4618c.2.1
                            have p4618_2 := h4618c.2.2.1
                            have p4618_3 := h4618c.2.2.2
                            linarith only [hlam, p4618_0]
                        · linarith only [h3093, h4491, h4612, h4617, hlam]
                      · linarith only [h3093, h4491, h4616, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4724 | h4724
      · linarith only [h0, h4, h4724, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4726 | h4726
        · linarith only [h0, h3093, h4726, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4728 | h4728
          · linarith only [h0, h3422, h4728, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4730 | h4730
            · linarith only [h1, h3633, h4730, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4732 | h4732
              · linarith only [h1, h4387, h4732, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4734 | h4734
                · linarith only [h2, h4491, h4734, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4736 | h4736
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4737 | h4737
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4738 | h4738
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4739 | h4739
                        · linarith only [h0, h3093, h4491, h4736, h4739, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h3633, h4, h4738, h4739, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4742 | h4742
                        · linarith only [h0, h3093, h4738, h4742, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            rcases p4744_3 (m.d 0 1) (by simp) with h4746 | h4746
                            · rcases p4744_3 (m.d 1 2) (by simp) with h4747 | h4747
                              · linarith only [h4747, hlam, p4744_0]
                              · rcases p4744_3 (m.d 1 3) (by simp) with h4749 | h4749
                                · linarith only [h1, h4749, hlam]
                                · linarith only [h4724, h4749, hlam]
                            · linarith only [h4746, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            rcases p4744_3 (m.d 0 1) (by simp) with h4753 | h4753
                            · rcases p4744_3 (m.d 1 2) (by simp) with h4754 | h4754
                              · linarith only [h0, h4754, hlam]
                              · rcases p4744_3 (m.d 1 3) (by simp) with h4756 | h4756
                                · linarith only [h4756, hlam, p4744_0]
                                · rcases p4744_3 (m.d 1 4) (by simp) with h4758 | h4758
                                  · linarith only [h2, h4758, hlam]
                                  · linarith only [h4730, h4758, hlam]
                            · linarith only [h4753, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            rcases p4744_3 (m.d 0 1) (by simp) with h4762 | h4762
                            · rcases p4744_3 (m.d 1 2) (by simp) with h4763 | h4763
                              · linarith only [h0, h4763, hlam]
                              · rcases p4744_3 (m.d 1 3) (by simp) with h4765 | h4765
                                · linarith only [h1, h4765, hlam]
                                · rcases p4744_3 (m.d 1 4) (by simp) with h4767 | h4767
                                  · linarith only [h4767, hlam, p4744_0]
                                  · rcases p4744_3 (m.d 1 5) (by simp) with h4769 | h4769
                                    · linarith only [h3, h4769, hlam]
                                    · linarith only [h4734, h4769, hlam]
                            · linarith only [h4762, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            rcases p4744_3 (m.d 0 1) (by simp) with h4773 | h4773
                            · rcases p4744_3 (m.d 1 2) (by simp) with h4774 | h4774
                              · linarith only [h0, h4774, hlam]
                              · rcases p4744_3 (m.d 1 3) (by simp) with h4776 | h4776
                                · linarith only [h1, h4776, hlam]
                                · rcases p4744_3 (m.d 1 4) (by simp) with h4778 | h4778
                                  · linarith only [h2, h4778, hlam]
                                  · rcases p4744_3 (m.d 1 5) (by simp) with h4780 | h4780
                                    · linarith only [h4780, hlam, p4744_0]
                                    · rcases h1emin with h4782 | h4782 | h4782 | h4782 | h4782
                                      · rcases h5bigk with h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c | h4783c
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4387, h4724, h4730, h4734, h4737, hc12, hc23, hlam, hphi, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h3422, hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4387, hlam, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4491, hlam, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h3, hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4728, hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4732, hlam, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4734, hlam, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          rcases p4783_3 (m.d 0 5) (by simp) with h4794 | h4794
                                          · linarith only [h3422, h4794, hlam]
                                          · rcases p4783_3 (m.d 1 5) (by simp) with h4796 | h4796
                                            · linarith only [h4728, h4796, hlam]
                                            · rcases p4783_3 (m.d 2 5) (by simp) with h4798 | h4798
                                              · rcases p4783_3 (m.d 3 5) (by simp) with h4799 | h4799
                                                · linarith only [h4737, h4799, hlam]
                                                · linarith only [h4387, h4799, hlam]
                                              · linarith only [h3422, h4798, hlam]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          rcases p4783_3 (m.d 0 5) (by simp) with h4803 | h4803
                                          · linarith only [h3422, h4803, hlam]
                                          · linarith only [h3, h4803, hlam]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h0, h3633, h4, h4738, h4742, hc12, hc45, hlam, hphi, ht23, ht34, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4738, hlam, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h3, h4724, h4730, h4734, h4737, hc12, hc23, hlam, hphi, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4724, h4730, h4734, h4737, hc12, hc23, hlam, hphi, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4737, hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [hlam, p4783_0]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h4742, hlam, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          rcases p4783_3 (m.d 0 5) (by simp) with h4814 | h4814
                                          · linarith only [h4491, h4814, hlam]
                                          · rcases p4783_3 (m.d 1 5) (by simp) with h4816 | h4816
                                            · linarith only [h4734, h4816, hlam]
                                            · rcases p4783_3 (m.d 2 5) (by simp) with h4818 | h4818
                                              · linarith only [h4738, h4818, hlam]
                                              · linarith only [h3422, h4818, hlam]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          rcases p4783_3 (m.d 0 5) (by simp) with h4821 | h4821
                                          · linarith only [h4491, h4821, hlam]
                                          · linarith only [h3, h4821, hlam]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h0, h3422, hc12, hc45, hlam, hphi, ht23, ht34, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [h0, h4, h4387, hc12, hc45, hlam, hphi, ht23, ht34, p4783_1]
                                        · have p4783_0 := h4783c.1
                                          have p4783_1 := h4783c.2.1
                                          have p4783_2 := h4783c.2.2.1
                                          have p4783_3 := h4783c.2.2.2
                                          linarith only [hlam, p4783_0]
                                      · linarith only [h4724, h4730, h4734, h4782, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4744_1]
                                      · linarith only [h4730, h4734, h4782, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4744_1]
                                      · linarith only [h4734, h4782, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4744_1]
                                      · linarith only [h4782, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4744_1]
                            · linarith only [h4773, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h0, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h4724, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h4726, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h4728, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h1, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h4730, hlam, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h4732, hlam, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h2, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h2, h4491, hc13, hc45, hlam, hphi, ht34, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h4734, hlam, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h3, hlam, p4744_0]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h3, h4724, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4744_1]
                          · have p4744_0 := h4744c.1
                            have p4744_1 := h4744c.2.1
                            have p4744_2 := h4744c.2.2.1
                            have p4744_3 := h4744c.2.2.2
                            linarith only [hlam, p4744_0]
                    · linarith only [h0, h3633, h4, h4736, h4737, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4853 | h4853
                    · linarith only [h0, h4, h4387, h4736, h4853, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4855 | h4855
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4856 | h4856
                        · rcases h1bigk with h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c | h4857c
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            rcases p4857_3 (m.d 0 1) (by simp) with h4859 | h4859
                            · rcases p4857_3 (m.d 1 2) (by simp) with h4860 | h4860
                              · linarith only [h4860, hlam, p4857_0]
                              · rcases p4857_3 (m.d 1 3) (by simp) with h4862 | h4862
                                · linarith only [h1, h4862, hlam]
                                · linarith only [h4724, h4862, hlam]
                            · linarith only [h4859, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            rcases p4857_3 (m.d 0 1) (by simp) with h4866 | h4866
                            · rcases p4857_3 (m.d 1 2) (by simp) with h4867 | h4867
                              · linarith only [h0, h4867, hlam]
                              · rcases p4857_3 (m.d 1 3) (by simp) with h4869 | h4869
                                · linarith only [h4869, hlam, p4857_0]
                                · rcases p4857_3 (m.d 1 4) (by simp) with h4871 | h4871
                                  · linarith only [h2, h4871, hlam]
                                  · linarith only [h4730, h4871, hlam]
                            · linarith only [h4866, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            rcases p4857_3 (m.d 0 1) (by simp) with h4875 | h4875
                            · rcases p4857_3 (m.d 1 2) (by simp) with h4876 | h4876
                              · linarith only [h0, h4876, hlam]
                              · rcases p4857_3 (m.d 1 3) (by simp) with h4878 | h4878
                                · linarith only [h1, h4878, hlam]
                                · rcases p4857_3 (m.d 1 4) (by simp) with h4880 | h4880
                                  · linarith only [h4880, hlam, p4857_0]
                                  · rcases p4857_3 (m.d 1 5) (by simp) with h4882 | h4882
                                    · linarith only [h3, h4882, hlam]
                                    · linarith only [h4734, h4882, hlam]
                            · linarith only [h4875, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            rcases p4857_3 (m.d 0 1) (by simp) with h4886 | h4886
                            · rcases p4857_3 (m.d 1 2) (by simp) with h4887 | h4887
                              · linarith only [h0, h4887, hlam]
                              · rcases p4857_3 (m.d 1 3) (by simp) with h4889 | h4889
                                · linarith only [h1, h4889, hlam]
                                · rcases p4857_3 (m.d 1 4) (by simp) with h4891 | h4891
                                  · linarith only [h2, h4891, hlam]
                                  · rcases p4857_3 (m.d 1 5) (by simp) with h4893 | h4893
                                    · linarith only [h4893, hlam, p4857_0]
                                    · rcases h1emin with h4895 | h4895 | h4895 | h4895 | h4895
                                      · rcases h5bigk with h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c | h4896c
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4491, h4728, h4736, h4855, hc12, hc34, hlam, hphi, ht23, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h3422, hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4387, hlam, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4491, hlam, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h3, hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4728, hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4732, hlam, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4734, hlam, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          rcases p4896_3 (m.d 0 5) (by simp) with h4907 | h4907
                                          · linarith only [h3422, h4907, hlam]
                                          · rcases p4896_3 (m.d 1 5) (by simp) with h4909 | h4909
                                            · linarith only [h4728, h4909, hlam]
                                            · rcases p4896_3 (m.d 2 5) (by simp) with h4911 | h4911
                                              · rcases p4896_3 (m.d 3 5) (by simp) with h4912 | h4912
                                                · rcases p4896_3 (m.d 4 5) (by simp) with h4913 | h4913
                                                  · linarith only [h4855, h4913, hlam]
                                                  · linarith only [h4491, h4913, hlam]
                                                · linarith only [h4387, h4912, hlam]
                                              · linarith only [h3422, h4911, hlam]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          rcases p4896_3 (m.d 0 5) (by simp) with h4918 | h4918
                                          · linarith only [h3422, h4918, hlam]
                                          · linarith only [h3, h4918, hlam]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4853, hlam, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h2, h4491, h4724, h4730, h4853, h4856, hc12, hc34, hlam, hphi, ht23, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          rcases p4896_3 (m.d 0 5) (by simp) with h4924 | h4924
                                          · linarith only [h4387, h4924, hlam]
                                          · rcases p4896_3 (m.d 1 5) (by simp) with h4926 | h4926
                                            · linarith only [h4732, h4926, hlam]
                                            · rcases p4896_3 (m.d 2 5) (by simp) with h4928 | h4928
                                              · linarith only [h4853, h4928, hlam]
                                              · linarith only [h3422, h4928, hlam]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          rcases p4896_3 (m.d 0 5) (by simp) with h4931 | h4931
                                          · linarith only [h4387, h4931, hlam]
                                          · linarith only [h3, h4931, hlam]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h0, h3422, h4856, hc12, hc34, hlam, hphi, ht23, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h2, h4491, h4724, h4730, h4856, hc12, hc34, hlam, hphi, ht23, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h3, h4724, h4730, h4734, h4736, h4855, hc12, hc34, hlam, hphi, ht23, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4724, h4730, h4734, h4736, h4855, hc12, hc34, hlam, hphi, ht23, p4896_1]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4855, hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [h4856, hlam, p4896_0]
                                        · have p4896_0 := h4896c.1
                                          have p4896_1 := h4896c.2.1
                                          have p4896_2 := h4896c.2.2.1
                                          have p4896_3 := h4896c.2.2.2
                                          linarith only [hlam, p4896_0]
                                      · linarith only [h4724, h4730, h4734, h4895, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4857_1]
                                      · linarith only [h4730, h4734, h4895, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4857_1]
                                      · linarith only [h4734, h4895, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4857_1]
                                      · linarith only [h4895, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4857_1]
                            · linarith only [h4886, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h0, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h4724, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h4726, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h4728, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h1, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h4730, hlam, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h4732, hlam, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h2, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h2, h4491, h4736, h4855, hc12, hc34, hlam, hphi, ht23, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h2, h4491, h4736, h4855, hc13, hc34, hlam, hphi, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h4734, hlam, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h3, hlam, p4857_0]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h3, h4491, h4736, h4855, hc12, hc34, hlam, hphi, ht23, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h3, h4491, h4724, h4736, h4855, hc12, hc34, hlam, hphi, ht23, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [h3, h4491, h4736, h4855, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4857_1]
                          · have p4857_0 := h4857c.1
                            have p4857_1 := h4857c.2.1
                            have p4857_2 := h4857c.2.2.1
                            have p4857_3 := h4857c.2.2.2
                            linarith only [hlam, p4857_0]
                        · linarith only [h4736, h4855, h4856, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4968 | h4968
                        · linarith only [h0, h4, h4736, h4855, h4968, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h4, h4736, h4968, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3093 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3422 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h3633 | h3633
  · exact r1l7_21_15_H_I_L_I_s3_x1_x1_x1_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h3093 h3422 h3633
  · exact r1l7_21_15_H_I_L_I_s3_x1_x1_x1_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h3093 h3422 h3633

set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3093 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h3422 | h3422
  · exact r1l7_21_15_H_I_L_I_s3_x1_x1_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h3093 h3422
  · exact r1l7_21_15_H_I_L_I_s3_x1_x1_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h3093 h3422

set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h3093 | h3093
  · exact r1l7_21_15_H_I_L_I_s3_x1_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h3093
  · exact r1l7_21_15_H_I_L_I_s3_x1_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4 h3093

set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_15_H_I_L_I_s3_x0 m hb1 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_21_15_H_I_L_I_s3_x1 m hb1 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 10182000 in
set_option maxHeartbeats 10182000 in
theorem r1l7_21_15_H_I_L_I_s2 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_15_H_I_L_I_s3 m hb1 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4971 | h4971
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4972 | h4972
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4973 | h4973
        · linarith only [h0, h3, h4973, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4975 | h4975
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4976 | h4976
            · linarith only [h1, h3, h4976, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4978 | h4978
              · linarith only [h2, h3, h4978, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4980 | h4980
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4981 | h4981
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4982 | h4982
                    · linarith only [h0, h4971, h4973, h4975, h4982, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4984 | h4984
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4985 | h4985
                        · linarith only [h1, h4976, h4985, hlam]
                        · linarith only [h0, h3, h4980, h4985, hc23, hc35, hlam, hphi]
                      · linarith only [h4975, h4976, h4984, hc13, hc35, hlam, hphi]
                  · linarith only [h4972, h4973, h4981, hc12, hc25, hlam, hphi]
                · linarith only [h4971, h4973, h4980, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4991 | h4991
            · linarith only [h1, h3, h4991, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4993 | h4993
              · linarith only [h0, h3, h4972, h4993, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4995 | h4995
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4996 | h4996
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4997 | h4997
                    · linarith only [h0, h4973, h4997, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4999 | h4999
                      · linarith only [h1, h4975, h4999, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5001 | h5001
                        · linarith only [h0, h1, h3, h4975, h4991, h5001, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h3, h4995, h5001, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h4972, h4995, h4996, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h4971, h4973, h4995, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5006 | h5006
        · linarith only [h0, h3, h5006, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5008 | h5008
          · linarith only [h4971, h4972, h5008, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5010 | h5010
            · linarith only [h2, h3, h4971, h4972, h5010, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5012 | h5012
              · linarith only [h2, h3, h5012, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5014 | h5014
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5015 | h5015
                  · linarith only [h0, h4972, h5015, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5017 | h5017
                    · linarith only [h0, h5006, h5017, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5019 | h5019
                      · linarith only [h1, h3, h5008, h5017, h5019, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5021 | h5021
                        · linarith only [h1, h5010, h5021, hlam]
                        · linarith only [h0, h3, h5014, h5021, hc23, hc35, hlam, hphi]
                · linarith only [h4971, h4972, h5014, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5025 | h5025
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5026 | h5026
        · linarith only [h1, h3, h4971, h5026, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5028 | h5028
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5029 | h5029
            · linarith only [h1, h3, h5029, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5031 | h5031
              · linarith only [h1, h3, h4971, h5025, h5031, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5033 | h5033
                · linarith only [h0, h3, h4971, h5033, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5035 | h5035
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5036 | h5036
                    · linarith only [h0, h3, h5026, h5036, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5038 | h5038
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5039 | h5039
                        · linarith only [h1, h3, h4971, h5029, h5039, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5041 | h5041
                          · linarith only [h1, h3, h5031, h5033, h5035, h5041, hlam]
                          · linarith only [h1, h3, h5033, h5035, h5041, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h5028, h5033, h5035, h5038, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h4971, h5025, h5029, h5035, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h4971, h5025, h5028, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5047 | h5047
        · linarith only [h0, h3, h5047, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5049 | h5049
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5050 | h5050
            · linarith only [h1, h3, h5050, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5052 | h5052
              · linarith only [h1, h3, h5049, h5052, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5054 | h5054
                · linarith only [h0, h4971, h5054, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5056 | h5056
                  · linarith only [h0, h3, h5025, h5056, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5058 | h5058
                    · linarith only [h0, h5047, h5058, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5060 | h5060
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5061 | h5061
                        · linarith only [h1, h5050, h5061, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5063 | h5063
                          · linarith only [h2, h3, h5052, h5063, hlam]
                          · linarith only [h1, h3, h5060, h5063, hc34, hc45, hlam, hphi]
                      · linarith only [h5049, h5050, h5060, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5067 | h5067
            · linarith only [h1, h3, h5067, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5069 | h5069
              · linarith only [h2, h3, h5069, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5071 | h5071
                · linarith only [h0, h4971, h5071, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5073 | h5073
                  · linarith only [h0, h3, h5025, h5073, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5075 | h5075
                    · linarith only [h0, h5047, h5075, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5077 | h5077
                      · linarith only [h1, h3, h5049, h5075, h5077, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5079 | h5079
                        · linarith only [h2, h3, h5067, h5077, h5079, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5081 | h5081
                          · linarith only [h2, h3, h5069, h5079, h5081, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5083 | h5083
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5084 | h5084
                              · linarith only [h0, h3, h5079, h5084, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h4971, h5049, h5083, h5084, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5087 | h5087
                              · linarith only [h0, h4971, h5067, h5083, h5087, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5089 | h5089
                                · linarith only [h2, h3, h5071, h5077, h5081, h5089, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5091 | h5091
                                  · linarith only [h0, h4971, h5083, h5089, h5091, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h4971, h5083, h5091, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
