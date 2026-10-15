import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10268000 in
set_option maxHeartbeats 10268000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_22_13_15_H_I_L_I_L_I_s1 m hb2 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h4381 | h4381
    · rcases m.htr 0 1 5 (by decide) (by decide) with h4382 | h4382
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4383 | h4383
        · linarith only [h0, h1, h4383, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4385 | h4385
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4386 | h4386
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4387 | h4387
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4388 | h4388
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4389 | h4389
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4390 | h4390
                    · linarith only [h0, h1, h4383, h4390, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4392 | h4392
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4393 | h4393
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4394 | h4394
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4395 | h4395
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4396 | h4396
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4397 | h4397
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4398 | h4398
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4399 | h4399
                                    · linarith only [h0, h1, h4390, h4392, h4399, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h0, h1, h4390, h4392, h4396, h4399, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h1, h4390, h4398, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h4390, h4397, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4404 | h4404
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4405 | h4405
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4406 | h4406
                                    · linarith only [h4392, h4396, h4406, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4408 | h4408
                                      · linarith only [h4392, h4396, h4404, h4408, hlam]
                                      · rcases h2bigk with h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h0, h1, h4390, hc12, hc23, hlam, hphi, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4383, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h0, h1, h4390, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h0, h1, h4390, h4405, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h0, hlam, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4390, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h0, h1, h4390, h4404, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h0, h1, h4390, h4405, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          rcases p4410_3 (m.d 0 2) (by simp) with h4424 | h4424
                                          · linarith only [h4383, h4424, hlam]
                                          · linarith only [h4385, h4424, hlam]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          rcases p4410_3 (m.d 0 2) (by simp) with h4427 | h4427
                                          · linarith only [h4383, h4427, hlam]
                                          · linarith only [h4386, h4427, hlam]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4385, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4392, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4404, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4406, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4386, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4393, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4405, hlam, p4410_0]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [h4386, h4404, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4410_1]
                                        · have p4410_0 := h4410c.1
                                          have p4410_1 := h4410c.2.1
                                          have p4410_2 := h4410c.2.2.1
                                          have p4410_3 := h4410c.2.2.2
                                          linarith only [hlam, p4410_0]
                                  · linarith only [h0, h1, h4390, h4405, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h4385, h4389, h4390, h4392, h4396, h4404, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h4395, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h4394, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h4386, h4390, h4392, h4393, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1, h4385, h4390, h4392, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4446 | h4446
                    · linarith only [h0, h1, h4383, h4446, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4448 | h4448
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4449 | h4449
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4450 | h4450
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4451 | h4451
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4452 | h4452
                              · linarith only [h4381, h4389, h4452, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4454 | h4454
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4455 | h4455
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4456 | h4456
                                    · linarith only [h0, h1, h4389, h4446, h4448, h4456, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4458 | h4458
                                      · linarith only [h4387, h4389, h4458, hlam]
                                      · rcases h2bigk with h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4449, hc02, hc25, hlam, hphi, ht0b, ht5b, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4383, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h0, h1, h4446, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h0, h1, h4446, h4455, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h0, hlam, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4446, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h0, h1, h4446, h4454, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h0, h1, h4446, h4455, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          rcases p4460_3 (m.d 0 2) (by simp) with h4474 | h4474
                                          · linarith only [h4383, h4474, hlam]
                                          · linarith only [h4385, h4474, hlam]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          rcases p4460_3 (m.d 0 2) (by simp) with h4477 | h4477
                                          · linarith only [h4383, h4477, hlam]
                                          · linarith only [h4386, h4477, hlam]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4385, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4448, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4454, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4456, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4386, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4449, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h4455, hlam, p4460_0]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [h0, h4449, h4454, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4460_1]
                                        · have p4460_0 := h4460c.1
                                          have p4460_1 := h4460c.2.1
                                          have p4460_2 := h4460c.2.2.1
                                          have p4460_3 := h4460c.2.2.2
                                          linarith only [hlam, p4460_0]
                                  · linarith only [h0, h1, h4446, h4455, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h4446, h4448, h4454, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h4448, h4451, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h4448, h4450, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h4386, h4448, h4449, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h4385, h4446, h4448, hc12, hc23, hlam, hphi]
                · linarith only [h1, h4382, h4388, hlam]
              · linarith only [h1, h4381, h4387, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4498 | h4498
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4499 | h4499
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4500 | h4500
                  · linarith only [h4385, h4386, h4500, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4502 | h4502
                    · linarith only [h0, h1, h4383, h4502, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4504 | h4504
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4505 | h4505
                        · linarith only [h0, h4386, h4505, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4507 | h4507
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4508 | h4508
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4509 | h4509
                              · linarith only [h1, h4381, h4500, h4502, h4509, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4511 | h4511
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4512 | h4512
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4513 | h4513
                                    · linarith only [h1, h4381, h4386, h4500, h4502, h4504, h4513, hc02, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4515 | h4515
                                      · linarith only [h0, h4386, h4498, h4504, h4513, h4515, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                      · rcases h2bigk with h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c | h4517c
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4504, h4511, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4383, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4386, h4511, h4513, hc34, hc45, hlam, hphi, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4386, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h0, hlam, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4502, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4382, h4505, h4511, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4505, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          rcases p4517_3 (m.d 0 2) (by simp) with h4531 | h4531
                                          · linarith only [h4383, h4531, hlam]
                                          · linarith only [h4385, h4531, hlam]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h0, h4386, h4504, h4511, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4385, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4504, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4511, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4513, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h0, h4504, h4511, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4504, h4511, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4512, hlam, p4517_0]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [h4511, h4513, hc34, hc45, hlam, hphi, p4517_1]
                                        · have p4517_0 := h4517c.1
                                          have p4517_1 := h4517c.2.1
                                          have p4517_2 := h4517c.2.2.1
                                          have p4517_3 := h4517c.2.2.2
                                          linarith only [hlam, p4517_0]
                                  · linarith only [h1, h4382, h4502, h4508, h4512, hlam]
                                · linarith only [h0, h1, h4502, h4511, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h4382, h4504, h4505, h4508, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h4382, h4504, h4505, h4507, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h4385, h4502, h4504, hc12, hc23, hlam, hphi]
                · linarith only [h1, h4382, h4499, hlam]
              · linarith only [h0, h1, h4385, h4498, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4552 | h4552
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4553 | h4553
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4554 | h4554
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4555 | h4555
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4556 | h4556
                    · linarith only [h0, h1, h4383, h4556, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4558 | h4558
                      · linarith only [h0, h4385, h4558, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4560 | h4560
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4561 | h4561
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4562 | h4562
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4563 | h4563
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4564 | h4564
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4565 | h4565
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4566 | h4566
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4567 | h4567
                                      · rcases h2bigk with h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c | h4568c
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4385, hc12, hc24, hlam, hphi, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4383, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4385, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h1, h4381, h4385, h4556, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h0, hlam, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4556, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4558, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h0, h1, h4556, h4565, h4567, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h0, h4385, h4560, h4565, h4567, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          rcases p4568_3 (m.d 0 2) (by simp) with h4583 | h4583
                                          · linarith only [h4383, h4583, hlam]
                                          · linarith only [h4552, h4583, hlam]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h0, h4560, h4565, h4567, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4560, h4565, h4567, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4564, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          rcases p4568_3 (m.d 0 2) (by simp) with h4590 | h4590
                                          · linarith only [h4385, h4590, hlam]
                                          · linarith only [h4552, h4590, hlam]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4552, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4560, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4565, hlam, p4568_0]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [h4566, hlam, p4568_1]
                                        · have p4568_0 := h4568c.1
                                          have p4568_1 := h4568c.2.1
                                          have p4568_2 := h4568c.2.2.1
                                          have p4568_3 := h4568c.2.2.2
                                          linarith only [hlam, p4568_0]
                                      · linarith only [h1, h4381, h4556, h4563, h4567, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h4381, h4556, h4563, h4566, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h4381, h4556, h4558, h4565, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h4381, h4556, h4558, h4560, h4564, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h4381, h4555, h4558, h4560, h4563, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h1, h4560, h4562, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h4381, h4558, h4560, h4561, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h4385, h4552, h4560, hc12, hc24, hlam, hphi]
                  · linarith only [h4385, h4552, h4555, hlam]
                · linarith only [h1, h4381, h4385, h4552, h4554, hlam]
              · linarith only [h1, h4381, h4553, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4609 | h4609
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4610 | h4610
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4611 | h4611
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4612 | h4612
                    · linarith only [h0, h1, h4383, h4612, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4614 | h4614
                      · linarith only [h0, h4385, h4614, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4616 | h4616
                        · linarith only [h0, h4552, h4616, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4618 | h4618
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4619 | h4619
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4620 | h4620
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4621 | h4621
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4622 | h4622
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4623 | h4623
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4624 | h4624
                                      · rcases h2bigk with h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c | h4625c
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4552, hc12, hc25, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4383, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4385, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4552, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h0, hlam, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4612, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4614, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4616, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4381, h4385, h4618, h4624, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h0, h4552, hc12, hc23, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hc12, hc24, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4621, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h0, h4552, h4621, hc12, hc23, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hc12, hc25, hlam, hphi, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4622, hlam, p4625_0]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [h4623, hlam, p4625_1]
                                        · have p4625_0 := h4625c.1
                                          have p4625_1 := h4625c.2.1
                                          have p4625_2 := h4625c.2.2.1
                                          have p4625_3 := h4625c.2.2.2
                                          linarith only [hlam, p4625_0]
                                      · linarith only [h1, h4381, h4612, h4620, h4624, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h4381, h4612, h4620, h4623, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h4381, h4612, h4620, h4622, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h4381, h4612, h4620, h4621, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h4381, h4611, h4612, h4614, h4620, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h4619, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h4618, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4658 | h4658
                    · linarith only [h0, h1, h4383, h4658, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4660 | h4660
                      · linarith only [h0, h1, h4385, h4660, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4662 | h4662
                        · linarith only [h0, h4552, h4662, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4664 | h4664
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4665 | h4665
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4666 | h4666
                              · linarith only [h1, h4381, h4611, h4658, h4666, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4668 | h4668
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4669 | h4669
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4670 | h4670
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4671 | h4671
                                      · linarith only [h4609, h4611, h4671, hlam]
                                      · rcases h2bigk with h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h0, h1, h4658, hc12, hc23, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4383, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4385, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4552, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h0, hlam, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4658, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4660, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4662, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4611, h4670, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h0, h4552, hc12, hc23, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hc12, hc24, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4668, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h0, h4552, h4668, hc12, hc23, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hc12, hc25, hlam, hphi, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4669, hlam, p4673_0]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [h4670, hlam, p4673_1]
                                        · have p4673_0 := h4673c.1
                                          have p4673_1 := h4673c.2.1
                                          have p4673_2 := h4673c.2.2.1
                                          have p4673_3 := h4673c.2.2.2
                                          linarith only [hlam, p4673_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4699 | h4699
                                      · linarith only [h0, h1, h4552, h4609, h4658, h4670, h4699, hc12, hc23, hlam, hphi]
                                      · rcases h2bigk with h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c | h4701c
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h0, h1, h4658, hc12, hc23, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4383, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4385, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4552, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h0, hlam, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4658, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4660, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4662, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h0, h4385, hc12, hc23, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h0, h4552, hc12, hc23, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4670, hc12, hc45, hlam, hphi, ht23, ht34, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4668, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4670, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hc12, hc25, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4669, hlam, p4701_0]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [h4385, h4670, hc04, hc45, hlam, hphi, p4701_1]
                                        · have p4701_0 := h4701c.1
                                          have p4701_1 := h4701c.2.1
                                          have p4701_2 := h4701c.2.2.1
                                          have p4701_3 := h4701c.2.2.2
                                          linarith only [hlam, p4701_0]
                                  · linarith only [h0, h1, h4658, h4669, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h4658, h4668, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h4381, h4660, h4665, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h4381, h4660, h4664, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h4382, h4610, hlam]
              · linarith only [h1, h4381, h4609, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4733 | h4733
        · linarith only [h0, h1, h4733, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4735 | h4735
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4736 | h4736
            · linarith only [h0, h4382, h4736, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4738 | h4738
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4739 | h4739
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4740 | h4740
                  · linarith only [h0, h4382, h4735, h4740, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4742 | h4742
                    · linarith only [h0, h1, h4733, h4742, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4744 | h4744
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4745 | h4745
                        · linarith only [h0, h4382, h4736, h4745, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4747 | h4747
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4748 | h4748
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4749 | h4749
                              · linarith only [h0, h4381, h4382, h4735, h4740, h4749, hlam]
                              · linarith only [h0, h4382, h4744, h4749, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h1, h4739, h4744, h4748, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1, h4744, h4747, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h4733, h4735, h4744, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4755 | h4755
                  · linarith only [h0, h1, h4735, h4739, h4755, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4757 | h4757
                    · linarith only [h0, h1, h4733, h4757, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4759 | h4759
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4760 | h4760
                        · linarith only [h0, h4736, h4760, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4762 | h4762
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4763 | h4763
                            · linarith only [h0, h1, h4739, h4757, h4759, h4763, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h4759, h4763, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h4759, h4762, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h4733, h4735, h4759, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h4735, h4738, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4769 | h4769
            · linarith only [h4381, h4382, h4735, h4769, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4771 | h4771
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4772 | h4772
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4773 | h4773
                  · linarith only [h4381, h4382, h4773, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4775 | h4775
                    · linarith only [h0, h4733, h4775, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4777 | h4777
                      · linarith only [h0, h4735, h4777, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4779 | h4779
                        · linarith only [h0, h4382, h4769, h4779, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4781 | h4781
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4782 | h4782
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4783 | h4783
                              · linarith only [h4381, h4382, h4735, h4773, h4782, h4783, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4785 | h4785
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4786 | h4786
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4787 | h4787
                                    · linarith only [h0, h4382, h4783, h4785, h4787, hc12, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4789 | h4789
                                      · linarith only [h4381, h4382, h4781, h4782, h4787, h4789, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · rcases h2bigk with h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c | h4791c
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4735, hc12, hc24, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4733, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4735, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4769, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h0, hlam, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4775, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4777, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4779, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h0, h4735, hc12, hc23, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4381, h4382, h4777, h4779, hc12, hc23, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hc12, hc24, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4785, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4787, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4787, hc12, hc45, hlam, hphi, ht23, ht34, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4786, hlam, p4791_0]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [h4787, hc24, hc45, hlam, hphi, p4791_1]
                                        · have p4791_0 := h4791c.1
                                          have p4791_1 := h4791c.2.1
                                          have p4791_2 := h4791c.2.2.1
                                          have p4791_3 := h4791c.2.2.2
                                          linarith only [hlam, p4791_0]
                                  · linarith only [h4733, h4772, h4786, hlam]
                                · linarith only [h1, h4381, h4775, h4781, h4785, hlam]
                            · linarith only [h1, h4381, h4772, h4777, h4782, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h4381, h4777, h4781, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4821 | h4821
                  · linarith only [h1, h4381, h4772, h4821, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4823 | h4823
                    · linarith only [h0, h1, h4772, h4823, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4825 | h4825
                      · linarith only [h0, h4735, h4825, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4827 | h4827
                        · linarith only [h0, h4769, h4827, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4829 | h4829
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4830 | h4830
                            · linarith only [h1, h4381, h4772, h4823, h4825, h4830, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h4381, h4825, h4830, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h4381, h4825, h4829, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h4381, h4771, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h4835 | h4835
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4836 | h4836
        · linarith only [h0, h1, h4836, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4838 | h4838
          · linarith only [h0, h4381, h4838, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4840 | h4840
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4841 | h4841
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4842 | h4842
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4843 | h4843
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4844 | h4844
                    · linarith only [h0, h1, h4836, h4840, h4844, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4846 | h4846
                      · linarith only [h0, h4381, h4838, h4846, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4848 | h4848
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4849 | h4849
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4850 | h4850
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4851 | h4851
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4852 | h4852
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4853 | h4853
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4854 | h4854
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4855 | h4855
                                      · rcases h2bigk with h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c | h4856c
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h0, h4848, h4853, h4855, hc01, hc45, hlam, hphi, ht0b, ht5b, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4836, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4838, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h0, h4381, h4846, h4853, h4855, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h0, hlam, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4844, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4846, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h0, h4381, h4846, h4853, h4855, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h0, h4838, h4848, h4853, h4855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          rcases p4856_3 (m.d 0 2) (by simp) with h4871 | h4871
                                          · linarith only [h4836, h4871, hlam]
                                          · linarith only [h4840, h4871, hlam]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h0, h4848, h4853, h4855, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4848, h4853, h4855, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4852, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          rcases p4856_3 (m.d 0 2) (by simp) with h4878 | h4878
                                          · linarith only [h4838, h4878, hlam]
                                          · linarith only [h4840, h4878, hlam]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4840, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4848, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4853, hlam, p4856_0]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [h4854, hlam, p4856_1]
                                        · have p4856_0 := h4856c.1
                                          have p4856_1 := h4856c.2.1
                                          have p4856_2 := h4856c.2.2.1
                                          have p4856_3 := h4856c.2.2.2
                                          linarith only [hlam, p4856_0]
                                      · linarith only [h0, h4381, h4844, h4848, h4849, h4854, h4855, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h4838, h4843, h4854, hlam]
                                  · linarith only [h0, h1, h4844, h4848, h4853, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h4381, h4844, h4848, h4849, h4852, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h4381, h4848, h4851, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h4381, h4848, h4849, h4850, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h4841, h4849, hlam]
                        · linarith only [h0, h4381, h4840, h4846, h4848, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h4381, h4840, h4843, hlam]
                · linarith only [h0, h1, h4840, h4842, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4896 | h4896
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4897 | h4897
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4898 | h4898
                    · linarith only [h0, h1, h4841, h4898, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4900 | h4900
                      · linarith only [h0, h1, h4838, h4841, h4900, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4902 | h4902
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4903 | h4903
                          · linarith only [h0, h1, h4841, h4898, h4902, h4903, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1, h4902, h4903, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h4381, h4840, h4900, h4902, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h1, h4840, h4841, h4897, hlam]
                · linarith only [h0, h1, h4840, h4896, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4909 | h4909
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4910 | h4910
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4911 | h4911
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4912 | h4912
                    · linarith only [h0, h1, h4836, h4912, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4914 | h4914
                      · linarith only [h0, h4838, h4914, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4916 | h4916
                        · linarith only [h0, h4840, h4916, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4918 | h4918
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4919 | h4919
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h4920 | h4920
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h4921 | h4921
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h4922 | h4922
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4923 | h4923
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4924 | h4924
                                      · rcases h2bigk with h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4840, hc12, hc25, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4836, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4838, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4840, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h0, hlam, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4912, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4914, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4916, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4381, h4914, hc01, hc23, hlam, hphi, ht12, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h0, h4840, hc12, hc23, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hc12, hc24, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4921, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h0, h4840, h4921, hc12, hc23, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hc12, hc25, hlam, hphi, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4922, hlam, p4925_0]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [h4923, hlam, p4925_1]
                                        · have p4925_0 := h4925c.1
                                          have p4925_1 := h4925c.2.1
                                          have p4925_2 := h4925c.2.2.1
                                          have p4925_3 := h4925c.2.2.2
                                          linarith only [hlam, p4925_0]
                                      · rcases h2bigk with h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c | h4951c
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h0, h4381, h4912, h4918, hc12, hc23, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4836, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4838, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4840, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h0, hlam, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4912, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4914, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4916, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4381, h4914, hc01, hc23, hlam, hphi, ht12, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h0, h4840, hc12, hc23, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hc12, hc24, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4921, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h0, h4840, h4921, hc12, hc23, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hc12, hc25, hlam, hphi, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4922, hlam, p4951_0]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [h4923, hlam, p4951_1]
                                        · have p4951_0 := h4951c.1
                                          have p4951_1 := h4951c.2.1
                                          have p4951_2 := h4951c.2.2.1
                                          have p4951_3 := h4951c.2.2.2
                                          linarith only [hlam, p4951_0]
                                    · linarith only [h0, h4381, h4835, h4838, h4918, h4920, h4923, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h4381, h4912, h4918, h4922, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h4381, h4912, h4918, h4921, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h4381, h4835, h4916, h4920, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h4381, h4835, h4916, h4918, h4919, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h4835, h4909, h4916, h4918, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h4381, h4835, h4911, hlam]
                · linarith only [h1, h4835, h4910, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4985 | h4985
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4986 | h4986
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4987 | h4987
                    · linarith only [h0, h1, h4909, h4987, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4989 | h4989
                      · linarith only [h0, h4838, h4989, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4991 | h4991
                        · linarith only [h0, h4840, h4991, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4993 | h4993
                          · linarith only [h1, h4835, h4909, h4987, h4991, h4993, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h4835, h4991, h4993, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h4835, h4909, h4986, hlam]
                · linarith only [h1, h4835, h4985, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4998 | h4998
        · linarith only [h0, h1, h4998, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5000 | h5000
          · linarith only [h0, h4381, h5000, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5002 | h5002
            · linarith only [h0, h4835, h5002, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5004 | h5004
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5005 | h5005
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5006 | h5006
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5007 | h5007
                    · linarith only [h0, h1, h4998, h5007, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5009 | h5009
                      · linarith only [h0, h1, h5000, h5006, h5007, h5009, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5011 | h5011
                        · linarith only [h0, h4835, h5002, h5011, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5013 | h5013
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5014 | h5014
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5015 | h5015
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5016 | h5016
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5017 | h5017
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5018 | h5018
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5019 | h5019
                                      · rcases h2bigk with h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c | h5020c
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h0, h4835, h5007, h5013, h5015, hc12, hc23, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h4998, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5000, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5002, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h0, hlam, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5007, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5009, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5011, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h4835, h5009, h5015, hc01, hc23, hlam, hphi, ht12, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h0, h4835, h5011, hc12, hc23, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hc12, hc24, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5016, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h0, h4835, h5011, h5016, hc12, hc23, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hc12, hc25, hlam, hphi, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5017, hlam, p5020_0]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [h5018, hlam, p5020_1]
                                        · have p5020_0 := h5020c.1
                                          have p5020_1 := h5020c.2.1
                                          have p5020_2 := h5020c.2.2.1
                                          have p5020_3 := h5020c.2.2.2
                                          linarith only [hlam, p5020_0]
                                      · rcases h2bigk with h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h0, h4835, h5013, h5015, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h4998, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5000, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5002, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h0, hlam, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5007, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5009, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5011, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hc02, hc23, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hc12, hc23, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h0, h5000, hc12, hc23, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h0, h5002, hc12, hc23, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h0, hc12, hc24, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hc12, hc24, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5016, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h4835, h5011, h5016, hc01, hc23, hlam, hphi, ht12, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hc12, hc25, hlam, hphi, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5017, hlam, p5046_0]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [h5018, hlam, p5046_1]
                                        · have p5046_0 := h5046c.1
                                          have p5046_1 := h5046c.2.1
                                          have p5046_2 := h5046c.2.2.1
                                          have p5046_3 := h5046c.2.2.2
                                          linarith only [hlam, p5046_0]
                                    · linarith only [h0, h4998, h5000, h5004, h5006, h5018, hc12, hc23, hlam, hphi]
                                  · linarith only [h0, h1, h5007, h5017, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h4835, h5007, h5013, h5015, h5016, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h4381, h5004, h5006, h5015, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h1, h5014, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5004, h5013, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5078 | h5078
                    · linarith only [h0, h4381, h5006, h5078, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5080 | h5080
                      · linarith only [h0, h4381, h5006, h5080, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5082 | h5082
                        · linarith only [h0, h5002, h5082, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5084 | h5084
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5085 | h5085
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5086 | h5086
                              · linarith only [h0, h4381, h5006, h5078, h5084, h5086, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h4381, h5086, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h5005, h5085, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h5084, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5091 | h5091
                  · linarith only [h5004, h5005, h5091, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5093 | h5093
                    · linarith only [h0, h1, h5005, h5093, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5095 | h5095
                      · linarith only [h0, h4381, h5091, h5095, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5097 | h5097
                        · linarith only [h0, h5002, h5097, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5099 | h5099
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5100 | h5100
                            · linarith only [h0, h4381, h5004, h5005, h5093, h5100, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h5100, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h5004, h5099, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5104 | h5104
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5105 | h5105
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5106 | h5106
                    · linarith only [h0, h4998, h5106, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5108 | h5108
                      · linarith only [h0, h5000, h5108, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5110 | h5110
                        · linarith only [h0, h5002, h5110, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5112 | h5112
                          · linarith only [h0, h4835, h5004, h5104, h5106, h5112, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5112, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h5004, h5104, h5105, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5116 | h5116
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5117 | h5117
                    · linarith only [h0, h1, h5104, h5117, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5119 | h5119
                      · linarith only [h0, h5000, h5119, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5121 | h5121
                        · linarith only [h0, h5002, h5121, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5123 | h5123
                          · linarith only [h0, h1, h5004, h5117, h5123, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5123, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5126 | h5126
                    · linarith only [h0, h1, h5004, h5116, h5126, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5128 | h5128
                      · linarith only [h0, h1, h5000, h5004, h5128, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5130 | h5130
                        · linarith only [h0, h4835, h5002, h5130, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5132 | h5132
                          · linarith only [h0, h1, h5004, h5126, h5132, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5132, hc12, hc34, hlam, hphi, ht23]

end R2N4
