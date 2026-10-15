import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S6
import Jsp000404.R1LeavesN7_20S12
import Jsp000404.R1LeavesN7_20S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3669 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3670 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3671 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h4330 | h4330
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4331 | h4331
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4332 | h4332
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4333 | h4333
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4334 | h4334
          · linarith only [h3667, h3671, h4334, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4336 | h4336
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4337 | h4337
              · linarith only [h3668, h3671, h4337, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4339 | h4339
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4340 | h4340
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4341 | h4341
                    · rcases h2bigk with h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c | h4342c
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h0, hlam, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h0, h4339, h4341, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h0, h4337, h4339, h4341, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        rcases p4342_3 (m.d 0 2) (by simp) with h4347 | h4347
                        · rcases p4342_3 (m.d 1 2) (by simp) with h4348 | h4348
                          · rcases p4342_3 (m.d 2 3) (by simp) with h4349 | h4349
                            · linarith only [h3668, h4349, hlam]
                            · linarith only [h4339, h4349, hlam]
                          · linarith only [h4333, h4348, hlam]
                        · linarith only [h4347, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4339, h4341, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4337, h4339, h4341, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        rcases p4342_3 (m.d 0 2) (by simp) with h4358 | h4358
                        · linarith only [h0, h4358, hlam]
                        · linarith only [h3670, h4358, hlam]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h3668, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4331, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4337, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h3667, h4332, h4337, h4339, h4341, hc01, hc45, hlam, hphi, ht0b, ht5b, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h3669, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4332, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h0, h3667, h4332, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h0, h3667, h4332, h4339, h4341, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h3670, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4333, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4339, hlam, p4342_1]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [h4340, hlam, p4342_0]
                      · have p4342_0 := h4342c.1
                        have p4342_1 := h4342c.2.1
                        have p4342_2 := h4342c.2.2.1
                        have p4342_3 := h4342c.2.2.2
                        linarith only [hlam, p4342_0]
                    · linarith only [h3668, h3671, h4330, h4339, h4341, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h3667, h4336, h4340, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4378 | h4378
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4379 | h4379
                    · rcases h2bigk with h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c | h4380c
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h0, hlam, p4380_1]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        rcases p4380_3 (m.d 0 2) (by simp) with h4383 | h4383
                        · rcases p4380_3 (m.d 1 2) (by simp) with h4384 | h4384
                          · rcases p4380_3 (m.d 2 3) (by simp) with h4385 | h4385
                            · linarith only [h4385, hlam, p4380_0]
                            · rcases p4380_3 (m.d 2 4) (by simp) with h4387 | h4387
                              · linarith only [h3669, h4387, hlam]
                              · linarith only [h4337, h4387, hlam]
                          · linarith only [h4331, h4384, hlam]
                        · linarith only [h4383, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h0, h4378, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4380_1]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        rcases p4380_3 (m.d 0 2) (by simp) with h4393 | h4393
                        · rcases p4380_3 (m.d 1 2) (by simp) with h4394 | h4394
                          · rcases p4380_3 (m.d 2 3) (by simp) with h4395 | h4395
                            · linarith only [h3668, h4395, hlam]
                            · rcases p4380_3 (m.d 2 4) (by simp) with h4397 | h4397
                              · linarith only [h3669, h4397, hlam]
                              · linarith only [h4378, h4397, hlam]
                          · linarith only [h4333, h4394, hlam]
                        · linarith only [h4393, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4380_1]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        rcases p4380_3 (m.d 0 2) (by simp) with h4404 | h4404
                        · linarith only [h0, h4404, hlam]
                        · linarith only [h3668, h4404, hlam]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h4378, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4380_1]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        rcases p4380_3 (m.d 0 2) (by simp) with h4408 | h4408
                        · linarith only [h0, h4408, hlam]
                        · linarith only [h3670, h4408, hlam]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h3668, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h4331, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h4337, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h4339, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h3669, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h4332, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h3667, h4332, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4380_1]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h0, h3667, h4332, h4339, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4380_1]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h3670, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h4333, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h0, h3670, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4380_1]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [h4378, hlam, p4380_0]
                      · have p4380_0 := h4380c.1
                        have p4380_1 := h4380c.2.1
                        have p4380_2 := h4380c.2.2.1
                        have p4380_3 := h4380c.2.2.2
                        linarith only [hlam, p4380_0]
                    · linarith only [h3671, h4330, h4379, hlam]
                  · linarith only [h0, h3667, h4336, h4378, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4428 | h4428
              · linarith only [h3671, h4330, h4331, h4334, h4336, h4428, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4430 | h4430
                · linarith only [h0, h3667, h4330, h4331, h4334, h4336, h4430, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4432 | h4432
                  · linarith only [h4332, h4336, h4432, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4434 | h4434
                    · rcases h2bigk with h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h0, hlam, p4435_1]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        rcases p4435_3 (m.d 0 2) (by simp) with h4438 | h4438
                        · rcases p4435_3 (m.d 1 2) (by simp) with h4439 | h4439
                          · rcases p4435_3 (m.d 2 3) (by simp) with h4440 | h4440
                            · linarith only [h4440, hlam, p4435_0]
                            · rcases p4435_3 (m.d 2 4) (by simp) with h4442 | h4442
                              · linarith only [h3669, h4442, hlam]
                              · linarith only [h4428, h4442, hlam]
                          · linarith only [h4331, h4439, hlam]
                        · linarith only [h4438, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        rcases p4435_3 (m.d 0 2) (by simp) with h4447 | h4447
                        · rcases p4435_3 (m.d 1 2) (by simp) with h4448 | h4448
                          · rcases p4435_3 (m.d 2 3) (by simp) with h4449 | h4449
                            · linarith only [h3668, h4449, hlam]
                            · rcases p4435_3 (m.d 2 4) (by simp) with h4451 | h4451
                              · linarith only [h4451, hlam, p4435_0]
                              · rcases p4435_3 (m.d 2 5) (by simp) with h4453 | h4453
                                · linarith only [h3670, h4453, hlam]
                                · linarith only [h4432, h4453, hlam]
                          · linarith only [h4332, h4448, hlam]
                        · linarith only [h4447, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        rcases p4435_3 (m.d 0 2) (by simp) with h4458 | h4458
                        · rcases p4435_3 (m.d 1 2) (by simp) with h4459 | h4459
                          · rcases p4435_3 (m.d 2 3) (by simp) with h4460 | h4460
                            · linarith only [h3668, h4460, hlam]
                            · rcases p4435_3 (m.d 2 4) (by simp) with h4462 | h4462
                              · linarith only [h3669, h4462, hlam]
                              · rcases p4435_3 (m.d 2 5) (by simp) with h4464 | h4464
                                · linarith only [h4464, hlam, p4435_0]
                                · rcases h4bigk with h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c | h4466c
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    rcases p4466_3 (m.d 0 4) (by simp) with h4468 | h4468
                                    · rcases p4466_3 (m.d 1 4) (by simp) with h4469 | h4469
                                      · linarith only [h3667, h4469, hlam]
                                      · rcases p4466_3 (m.d 2 4) (by simp) with h4471 | h4471
                                        · linarith only [h3669, h4471, hlam]
                                        · rcases p4466_3 (m.d 3 4) (by simp) with h4473 | h4473
                                          · rcases p4466_3 (m.d 4 5) (by simp) with h4474 | h4474
                                            · linarith only [h4330, h4474, hlam]
                                            · linarith only [h4336, h4474, hlam]
                                          · linarith only [h4334, h4473, hlam]
                                    · linarith only [h3667, h4468, hlam]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    rcases p4466_3 (m.d 0 4) (by simp) with h4479 | h4479
                                    · rcases p4466_3 (m.d 1 4) (by simp) with h4480 | h4480
                                      · linarith only [h3667, h4480, hlam]
                                      · linarith only [h4332, h4480, hlam]
                                    · linarith only [h3669, h4479, hlam]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h3671, hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h0, h3667, h4336, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h3667, hlam, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4336, hc24, hc45, hlam, hphi, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4334, hlam, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4336, hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h3669, hlam, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4332, hlam, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4428, hlam, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4432, hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4330, h4336, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    rcases p4466_3 (m.d 0 4) (by simp) with h4497 | h4497
                                    · linarith only [h3671, h4497, hlam]
                                    · linarith only [h3667, h4497, hlam]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    rcases p4466_3 (m.d 0 4) (by simp) with h4500 | h4500
                                    · linarith only [h3671, h4500, hlam]
                                    · linarith only [h3669, h4500, hlam]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4331, h4334, h4336, hc23, hc34, hlam, hphi, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4330, hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h0, h3667, h4330, h4331, h4334, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h0, h3667, h4330, h4428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4466_1]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [h4434, hlam, p4466_0]
                                  · have p4466_0 := h4466c.1
                                    have p4466_1 := h4466c.2.1
                                    have p4466_2 := h4466c.2.2.1
                                    have p4466_3 := h4466c.2.2.2
                                    linarith only [hlam, p4466_0]
                          · linarith only [h4333, h4459, hlam]
                        · linarith only [h4458, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4435_1]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        rcases p4435_3 (m.d 0 2) (by simp) with h4514 | h4514
                        · linarith only [h0, h4514, hlam]
                        · linarith only [h3668, h4514, hlam]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        rcases p4435_3 (m.d 0 2) (by simp) with h4517 | h4517
                        · linarith only [h0, h4517, hlam]
                        · linarith only [h3669, h4517, hlam]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        rcases p4435_3 (m.d 0 2) (by simp) with h4520 | h4520
                        · linarith only [h0, h4520, hlam]
                        · linarith only [h3670, h4520, hlam]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h3668, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h4331, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h4428, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h4430, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h3669, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h4332, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h3669, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4435_1]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h4432, hlam, p4435_1]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h3670, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h4333, hlam, p4435_0]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h4333, h4336, h4434, hc23, hc35, hlam, hphi, p4435_1]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [h0, h3667, h4330, h4333, h4336, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4435_1]
                      · have p4435_0 := h4435c.1
                        have p4435_1 := h4435c.2.1
                        have p4435_2 := h4435c.2.2.1
                        have p4435_3 := h4435c.2.2.2
                        linarith only [hlam, p4435_0]
                    · linarith only [h0, h3667, h3668, h3671, h4330, h4434, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h3670, h4333, hlam]
      · linarith only [h0, h3669, h4332, hlam]
    · linarith only [h0, h3668, h4331, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4542 | h4542
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4543 | h4543
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4544 | h4544
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4545 | h4545
          · linarith only [h3667, h3671, h4545, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4547 | h4547
            · linarith only [h3667, h4330, h4547, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4549 | h4549
              · linarith only [h3668, h3671, h4549, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4551 | h4551
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4552 | h4552
                  · linarith only [h3669, h4330, h4552, hlam]
                  · linarith only [h4549, h4551, h4552, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4555 | h4555
                  · linarith only [h3669, h4330, h4555, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4557 | h4557
                    · rcases h2bigk with h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c | h4558c
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h0, hlam, p4558_1]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        rcases p4558_3 (m.d 0 2) (by simp) with h4561 | h4561
                        · rcases p4558_3 (m.d 1 2) (by simp) with h4562 | h4562
                          · rcases p4558_3 (m.d 2 3) (by simp) with h4563 | h4563
                            · linarith only [h4563, hlam, p4558_0]
                            · rcases p4558_3 (m.d 2 4) (by simp) with h4565 | h4565
                              · linarith only [h3669, h4565, hlam]
                              · linarith only [h4549, h4565, hlam]
                          · linarith only [h4542, h4562, hlam]
                        · linarith only [h4561, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        rcases p4558_3 (m.d 0 2) (by simp) with h4570 | h4570
                        · rcases p4558_3 (m.d 1 2) (by simp) with h4571 | h4571
                          · rcases p4558_3 (m.d 2 3) (by simp) with h4572 | h4572
                            · linarith only [h3668, h4572, hlam]
                            · rcases p4558_3 (m.d 2 4) (by simp) with h4574 | h4574
                              · linarith only [h4574, hlam, p4558_0]
                              · rcases p4558_3 (m.d 2 5) (by simp) with h4576 | h4576
                                · linarith only [h3670, h4576, hlam]
                                · linarith only [h4555, h4576, hlam]
                          · linarith only [h4543, h4571, hlam]
                        · linarith only [h4570, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        rcases p4558_3 (m.d 0 2) (by simp) with h4581 | h4581
                        · rcases p4558_3 (m.d 1 2) (by simp) with h4582 | h4582
                          · rcases p4558_3 (m.d 2 3) (by simp) with h4583 | h4583
                            · linarith only [h3668, h4583, hlam]
                            · rcases p4558_3 (m.d 2 4) (by simp) with h4585 | h4585
                              · linarith only [h3669, h4585, hlam]
                              · rcases p4558_3 (m.d 2 5) (by simp) with h4587 | h4587
                                · linarith only [h4587, hlam, p4558_0]
                                · rcases h4bigk with h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c | h4589c
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h0, h4330, h4549, h4555, h4557, hc12, hc14, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4558_1, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4330, h4549, h4557, hc23, hc34, hlam, hphi, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h3671, hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4330, hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h3667, hlam, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h0, h3667, h4549, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4545, hlam, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4547, hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h3669, hlam, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4543, hlam, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4549, hlam, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4555, hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    rcases p4589_3 (m.d 0 4) (by simp) with h4605 | h4605
                                    · linarith only [h3671, h4605, hlam]
                                    · rcases p4589_3 (m.d 1 4) (by simp) with h4607 | h4607
                                      · linarith only [h4545, h4607, hlam]
                                      · rcases p4589_3 (m.d 2 4) (by simp) with h4609 | h4609
                                        · linarith only [h4549, h4609, hlam]
                                        · rcases p4589_3 (m.d 3 4) (by simp) with h4611 | h4611
                                          · rcases p4589_3 (m.d 4 5) (by simp) with h4612 | h4612
                                            · linarith only [h4557, h4612, hlam]
                                            · linarith only [h4330, h4612, hlam]
                                          · linarith only [h3671, h4611, hlam]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    rcases p4589_3 (m.d 0 4) (by simp) with h4616 | h4616
                                    · linarith only [h3671, h4616, hlam]
                                    · linarith only [h3667, h4616, hlam]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    rcases p4589_3 (m.d 0 4) (by simp) with h4619 | h4619
                                    · linarith only [h3671, h4619, hlam]
                                    · linarith only [h3669, h4619, hlam]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h3669, h4330, h4549, hc23, hc34, hlam, hphi, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h3667, h4543, h4549, h4557, hc23, hc34, hlam, hphi, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4543, h4549, h4557, hc23, hc34, hlam, hphi, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4549, h4557, hc23, hc34, hlam, hphi, p4589_1]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [h4557, hlam, p4589_0]
                                  · have p4589_0 := h4589c.1
                                    have p4589_1 := h4589c.2.1
                                    have p4589_2 := h4589c.2.2.1
                                    have p4589_3 := h4589c.2.2.2
                                    linarith only [hlam, p4589_0]
                          · linarith only [h4544, h4582, hlam]
                        · linarith only [h4581, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4558_1]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        rcases p4558_3 (m.d 0 2) (by simp) with h4633 | h4633
                        · linarith only [h0, h4633, hlam]
                        · linarith only [h3668, h4633, hlam]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        rcases p4558_3 (m.d 0 2) (by simp) with h4636 | h4636
                        · linarith only [h0, h4636, hlam]
                        · linarith only [h3669, h4636, hlam]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        rcases p4558_3 (m.d 0 2) (by simp) with h4639 | h4639
                        · linarith only [h0, h4639, hlam]
                        · linarith only [h3670, h4639, hlam]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h3668, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h4542, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h4549, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h4551, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h3669, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h4543, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h3667, h4543, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4558_1]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h4555, hlam, p4558_1]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h3670, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h4544, hlam, p4558_0]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h3670, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4558_1]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [h3670, h4330, h4557, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4558_1]
                      · have p4558_0 := h4558c.1
                        have p4558_1 := h4558c.2.1
                        have p4558_2 := h4558c.2.2.1
                        have p4558_3 := h4558c.2.2.2
                        linarith only [hlam, p4558_0]
                    · rcases h2bigk with h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c | h4657c
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h0, hlam, p4657_1]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        rcases p4657_3 (m.d 0 2) (by simp) with h4660 | h4660
                        · rcases p4657_3 (m.d 1 2) (by simp) with h4661 | h4661
                          · rcases p4657_3 (m.d 2 3) (by simp) with h4662 | h4662
                            · linarith only [h4662, hlam, p4657_0]
                            · rcases p4657_3 (m.d 2 4) (by simp) with h4664 | h4664
                              · linarith only [h3669, h4664, hlam]
                              · linarith only [h4549, h4664, hlam]
                          · linarith only [h4542, h4661, hlam]
                        · linarith only [h4660, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        rcases p4657_3 (m.d 0 2) (by simp) with h4669 | h4669
                        · rcases p4657_3 (m.d 1 2) (by simp) with h4670 | h4670
                          · rcases p4657_3 (m.d 2 3) (by simp) with h4671 | h4671
                            · linarith only [h3668, h4671, hlam]
                            · rcases p4657_3 (m.d 2 4) (by simp) with h4673 | h4673
                              · linarith only [h4673, hlam, p4657_0]
                              · rcases p4657_3 (m.d 2 5) (by simp) with h4675 | h4675
                                · linarith only [h3670, h4675, hlam]
                                · linarith only [h4555, h4675, hlam]
                          · linarith only [h4543, h4670, hlam]
                        · linarith only [h4669, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        rcases p4657_3 (m.d 0 2) (by simp) with h4680 | h4680
                        · rcases p4657_3 (m.d 1 2) (by simp) with h4681 | h4681
                          · rcases p4657_3 (m.d 2 3) (by simp) with h4682 | h4682
                            · linarith only [h3668, h4682, hlam]
                            · rcases p4657_3 (m.d 2 4) (by simp) with h4684 | h4684
                              · linarith only [h3669, h4684, hlam]
                              · rcases p4657_3 (m.d 2 5) (by simp) with h4686 | h4686
                                · linarith only [h4686, hlam, p4657_0]
                                · rcases h4bigk with h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c | h4688c
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h3671, h4557, hc14, hc45, hlam, hphi, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h3671, h4549, h4557, hc23, hc45, hlam, hphi, ht34, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h3671, hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4330, hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h3667, hlam, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h0, h3667, h4549, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4545, hlam, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4547, hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h3669, hlam, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4543, hlam, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4549, hlam, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4555, hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4557, hc04, hc45, hlam, hphi, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4557, hc14, hc45, hlam, hphi, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4549, h4557, hc23, hc45, hlam, hphi, ht34, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h4557, hlam, p4688_0]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    rcases p4688_3 (m.d 0 4) (by simp) with h4709 | h4709
                                    · linarith only [h4709, hlam, p4688_0]
                                    · rcases p4688_3 (m.d 1 4) (by simp) with h4711 | h4711
                                      · linarith only [h4547, h4711, hlam]
                                      · rcases p4688_3 (m.d 2 4) (by simp) with h4713 | h4713
                                        · linarith only [h4555, h4713, hlam]
                                        · rcases p4688_3 (m.d 3 4) (by simp) with h4715 | h4715
                                          · linarith only [h4557, h4715, hlam]
                                          · linarith only [h3671, h4715, hlam]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    rcases p4688_3 (m.d 0 4) (by simp) with h4718 | h4718
                                    · linarith only [h4330, h4718, hlam]
                                    · linarith only [h3667, h4718, hlam]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    rcases p4688_3 (m.d 0 4) (by simp) with h4721 | h4721
                                    · linarith only [h4330, h4721, hlam]
                                    · linarith only [h3669, h4721, hlam]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [h3668, h3671, hc23, hc45, hlam, hphi, ht34, p4688_1]
                                  · have p4688_0 := h4688c.1
                                    have p4688_1 := h4688c.2.1
                                    have p4688_2 := h4688c.2.2.1
                                    have p4688_3 := h4688c.2.2.2
                                    linarith only [hlam, p4688_0]
                          · linarith only [h4544, h4681, hlam]
                        · linarith only [h4680, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4657_1]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        rcases p4657_3 (m.d 0 2) (by simp) with h4730 | h4730
                        · linarith only [h0, h4730, hlam]
                        · linarith only [h3668, h4730, hlam]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        rcases p4657_3 (m.d 0 2) (by simp) with h4733 | h4733
                        · linarith only [h0, h4733, hlam]
                        · linarith only [h3669, h4733, hlam]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        rcases p4657_3 (m.d 0 2) (by simp) with h4736 | h4736
                        · linarith only [h0, h4736, hlam]
                        · linarith only [h3670, h4736, hlam]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h3668, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h4542, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h4549, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h4551, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h3669, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h4543, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h3667, h4543, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4657_1]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h4555, hlam, p4657_1]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h3670, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h4544, hlam, p4657_0]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h0, h3670, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4657_1]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [h0, h3670, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4657_1]
                      · have p4657_0 := h4657c.1
                        have p4657_1 := h4657c.2.1
                        have p4657_2 := h4657c.2.2.1
                        have p4657_3 := h4657c.2.2.2
                        linarith only [hlam, p4657_0]
        · linarith only [h0, h3670, h4544, hlam]
      · linarith only [h0, h3669, h4543, hlam]
    · linarith only [h0, h3667, h3668, h3671, h4542, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3669 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3670 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h3671 | h3671
  · exact r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x0_x0 m hb2 hb4 hg0 h3667 h3668 h3669 h3670 h3671
  · exact r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x0_x1 m hb2 hb4 hg0 h3667 h3668 h3669 h3670 h3671

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3669 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3670 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h4757 | h4757
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4758 | h4758
    · linarith only [h0, h3667, h3670, h4758, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4760 | h4760
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4761 | h4761
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4762 | h4762
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4763 | h4763
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4764 | h4764
              · linarith only [h0, h3667, h3670, h4758, h4762, h4764, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4766 | h4766
                · linarith only [h3668, h3670, h4762, h4766, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h3668, h3670, h4757, h4762, h4766, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h3668, h3670, h4757, h4762, h4763, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4770 | h4770
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4771 | h4771
              · linarith only [h0, h3667, h4762, h4771, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4773 | h4773
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4774 | h4774
                  · linarith only [h0, h3667, h3668, h4762, h4774, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4776 | h4776
                    · linarith only [h0, h3667, h4758, h4761, h4762, h4774, h4776, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h3667, h4762, h4776, hc14, hc45, hlam, hphi]
                · linarith only [h0, h3667, h4762, h4770, h4773, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4780 | h4780
              · linarith only [h0, h3667, h4762, h4780, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4782 | h4782
                · linarith only [h4760, h4770, h4782, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4784 | h4784
                  · linarith only [h0, h3667, h4757, h4760, h4762, h4770, h4784, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h3667, h4757, h4762, h4770, h4784, hc13, hc35, hlam, hphi]
        · linarith only [h0, h3669, h4761, hlam]
      · linarith only [h0, h3668, h4760, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4789 | h4789
    · linarith only [h0, h3667, h3670, h4789, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4791 | h4791
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4792 | h4792
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4793 | h4793
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4794 | h4794
            · linarith only [h0, h3667, h3668, h3670, h4757, h4793, h4794, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4796 | h4796
              · linarith only [h0, h3667, h3670, h4793, h4796, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4798 | h4798
                · linarith only [h3668, h3670, h4757, h4793, h4798, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4800 | h4800
                  · linarith only [h0, h3667, h3670, h4791, h4793, h4794, h4800, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4802 | h4802
                    · linarith only [h0, h3667, h3670, h4792, h4793, h4796, h4802, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4804 | h4804
                      · linarith only [h0, h3667, h3670, h4793, h4794, h4796, h4804, hc13, hc34, hlam, hphi]
                      · rcases h2bigk with h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h0, hlam, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h3670, h4793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h3670, h4793, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h3670, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          rcases p4806_3 (m.d 0 2) (by simp) with h4814 | h4814
                          · linarith only [h0, h4814, hlam]
                          · linarith only [h3668, h4814, hlam]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          rcases p4806_3 (m.d 0 2) (by simp) with h4817 | h4817
                          · linarith only [h0, h4817, hlam]
                          · linarith only [h3669, h4817, hlam]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h0, h3667, h3670, h4791, h4794, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h3668, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4791, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4798, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4800, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h3669, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4792, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h3669, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4802, hlam, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [hc02, hc25, hlam, hphi, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4793, hlam, p4806_0]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [h4793, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4806_1]
                        · have p4806_0 := h4806c.1
                          have p4806_1 := h4806c.2.1
                          have p4806_2 := h4806c.2.2.1
                          have p4806_3 := h4806c.2.2.2
                          linarith only [hlam, p4806_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4836 | h4836
            · linarith only [h0, h3667, h3668, h4757, h4793, h4836, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4838 | h4838
              · linarith only [h0, h3667, h4789, h4793, h4838, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4840 | h4840
                · linarith only [h3668, h4757, h4840, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4842 | h4842
                  · linarith only [h0, h3667, h4791, h4793, h4836, h4842, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h3667, h4791, h4793, h4836, h4842, hc23, hc35, hlam, hphi]
        · linarith only [h0, h3667, h3669, h3670, h4792, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h0, h3667, h3668, h4757, h4791, hlam]

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3669 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h3670 | h3670
  · exact r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x0 m hb2 hb4 hg0 h3667 h3668 h3669 h3670
  · exact r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x1 m hb2 hb4 hg0 h3667 h3668 h3669 h3670

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3669 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  linarith only [h0, h3667, h3669, hlam]

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3669 | h3669
  · exact r1l7_22_14_H_I_L_I_s2_x0_x0_x0 m hb2 hb4 hg0 h3667 h3668 h3669
  · exact r1l7_22_14_H_I_L_I_s2_x0_x0_x1 m hb2 hb4 hg0 h3667 h3668 h3669

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4848 | h4848
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4849 | h4849
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4850 | h4850
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4851 | h4851
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4852 | h4852
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4853 | h4853
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4854 | h4854
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4855 | h4855
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4856 | h4856
                  · linarith only [h0, h3667, h3668, h4852, h4856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h3667, h3668, h4851, h4852, h4856, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h3668, h4849, h4850, h4852, h4855, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h3667, h3668, h4852, h4853, h4854, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h0, h3667, h3668, h4852, h4853, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4862 | h4862
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4863 | h4863
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4864 | h4864
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4865 | h4865
                  · linarith only [h0, h3667, h4852, h4865, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h3667, h4851, h4852, h4864, h4865, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h3668, h4850, h4852, h4864, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h3667, h4849, h4862, h4863, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h4848, h4862, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4871 | h4871
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4872 | h4872
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4873 | h4873
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4874 | h4874
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4875 | h4875
                  · linarith only [h0, h3667, h4851, h4875, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4877 | h4877
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4878 | h4878
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4879 | h4879
                        · linarith only [h3667, h4851, h4872, h4879, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4881 | h4881
                          · linarith only [h3667, h4851, h4872, h4877, h4881, hlam]
                          · rcases h2bigk with h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c | h4883c
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h0, hlam, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h3668, hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h3668, h4871, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h3668, h4871, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h0, h3667, h3668, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              rcases p4883_3 (m.d 0 2) (by simp) with h4892 | h4892
                              · linarith only [h0, h4892, hlam]
                              · linarith only [h4848, h4892, hlam]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              rcases p4883_3 (m.d 0 2) (by simp) with h4895 | h4895
                              · linarith only [h0, h4895, hlam]
                              · linarith only [h4849, h4895, hlam]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h0, h3667, h4872, h4877, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4871, hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4871, h4877, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4871, h4877, h4879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4848, hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4872, hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4877, hlam, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4879, hlam, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4849, hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4873, hlam, p4883_0]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4878, hlam, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [h4849, h4877, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4883_1]
                            · have p4883_0 := h4883c.1
                              have p4883_1 := h4883c.2.1
                              have p4883_2 := h4883c.2.2.1
                              have p4883_3 := h4883c.2.2.2
                              linarith only [hlam, p4883_0]
                      · linarith only [h3668, h4849, h4878, hlam]
                    · linarith only [h3668, h4850, h4877, hlam]
                · linarith only [h0, h3667, h3668, h4850, h4871, h4874, hlam]
              · linarith only [h0, h4849, h4873, hlam]
            · linarith only [h0, h3667, h3668, h4871, h4872, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4918 | h4918
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4919 | h4919
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4920 | h4920
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4921 | h4921
                  · linarith only [h0, h3667, h4871, h4921, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4923 | h4923
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4924 | h4924
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4925 | h4925
                        · linarith only [h0, h3667, h4871, h4918, h4921, h4925, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4927 | h4927
                          · linarith only [h0, h3667, h4851, h4871, h4918, h4923, h4927, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases h2bigk with h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c | h4929c
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h0, hlam, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h3668, hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h0, h4871, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h0, h4871, h4923, h4925, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4871, hc02, hc23, hlam, hphi, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4871, hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4871, h4923, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4871, h4923, h4925, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              rcases p4929_3 (m.d 0 2) (by simp) with h4943 | h4943
                              · linarith only [h3668, h4943, hlam]
                              · linarith only [h4848, h4943, hlam]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              rcases p4929_3 (m.d 0 2) (by simp) with h4946 | h4946
                              · linarith only [h3668, h4946, hlam]
                              · linarith only [h4849, h4946, hlam]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4848, hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4918, hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4923, hlam, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4925, hlam, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4849, hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4919, hlam, p4929_0]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4924, hlam, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [h4849, h4923, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4929_1]
                            · have p4929_0 := h4929c.1
                              have p4929_1 := h4929c.2.1
                              have p4929_2 := h4929c.2.2.1
                              have p4929_3 := h4929c.2.2.2
                              linarith only [hlam, p4929_0]
                      · linarith only [h0, h3667, h4871, h4918, h4923, h4924, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h3667, h4871, h4918, h4923, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h3667, h4850, h4871, h4920, hlam]
              · linarith only [h0, h3667, h4849, h4918, h4919, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h4848, h4918, hlam]
      · linarith only [h0, h3667, h3668, h4850, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4965 | h4965
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4966 | h4966
        · linarith only [h0, h3667, h4849, h4966, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4968 | h4968
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4969 | h4969
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4970 | h4970
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4971 | h4971
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4972 | h4972
                  · linarith only [h0, h3667, h3668, h4966, h4968, h4972, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4974 | h4974
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4975 | h4975
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4976 | h4976
                        · linarith only [h0, h3667, h4849, h4969, h4970, h4972, h4976, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4978 | h4978
                          · linarith only [h0, h3667, h4849, h4969, h4970, h4972, h4974, h4978, hlam]
                          · rcases h2bigk with h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c | h4980c
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h0, hlam, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h3668, hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4849, h4968, h4975, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4849, hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4975, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              rcases p4980_3 (m.d 0 2) (by simp) with h4989 | h4989
                              · linarith only [h0, h4989, hlam]
                              · linarith only [h4848, h4989, hlam]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h0, h3667, h4849, h4969, h4974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h0, h3667, h4969, h4974, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4968, hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4968, h4974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h0, h3667, h4849, h4968, h4969, h4974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4848, hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4969, hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4974, hlam, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4976, hlam, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h0, h3667, h4969, h4970, h4974, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4970, hlam, p4980_0]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4975, hlam, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [h4968, h4974, h4975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4980_1]
                            · have p4980_0 := h4980c.1
                              have p4980_1 := h4980c.2.1
                              have p4980_2 := h4980c.2.2.1
                              have p4980_3 := h4980c.2.2.2
                              linarith only [hlam, p4980_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5008 | h5008
                        · linarith only [h0, h3667, h3668, h4969, h4972, h4975, h5008, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5010 | h5010
                          · linarith only [h0, h3667, h3668, h4969, h4972, h4974, h4975, h5010, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h3667, h3668, h4975, h5010, hc14, hc45, hlam, hphi]
                    · linarith only [h0, h3667, h3668, h4965, h4969, h4974, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h3667, h3668, h4965, h4968, h4971, hlam]
              · linarith only [h0, h3667, h3668, h4968, h4969, h4970, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h0, h3668, h4968, h4969, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5017 | h5017
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5018 | h5018
              · linarith only [h4849, h4968, h5018, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5020 | h5020
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5021 | h5021
                  · linarith only [h0, h3667, h4966, h4968, h5021, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5023 | h5023
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5024 | h5024
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5025 | h5025
                        · linarith only [h0, h3667, h5017, h5018, h5021, h5025, hlam]
                        · linarith only [h0, h3667, h5018, h5025, hc14, hc45, hlam, hphi]
                      · linarith only [h0, h3667, h4968, h5017, h5023, h5024, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h3667, h4968, h5017, h5023, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h3667, h4965, h4968, h5020, hlam]
            · linarith only [h0, h4848, h5017, hlam]
      · linarith only [h0, h3667, h3668, h4965, hlam]
  · linarith only [h0, h3667, h4848, hlam]

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3668 | h3668
  · exact r1l7_22_14_H_I_L_I_s2_x0_x0 m hb2 hb4 hg0 h3667 h3668
  · exact r1l7_22_14_H_I_L_I_s2_x0_x1 m hb2 hb4 hg0 h3667 h3668

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4bigk := hb4.1
  have h0 := hg0
  exact r1l7_22_14_H_I_L_I_s3 m hb2 hb4 h0 h3667

set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3667 | h3667
  · exact r1l7_22_14_H_I_L_I_s2_x0 m hb2 hb4 hg0 h3667
  · exact r1l7_22_14_H_I_L_I_s2_x1 m hb2 hb4 hg0 h3667

set_option maxHeartbeats 16586000 in
set_option maxHeartbeats 16586000 in
theorem r1l7_22_14_H_I_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_14_H_I_L_I_s0 m hb2 hb4 h0
  · exact r1l7_22_14_H_I_L_I_s2 m hb2 hb4 h0

end R2N4
