import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4344 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4345 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h4346 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 2 3 5 (by decide) (by decide) with h4347 | h4347
  · rcases m.htr 2 4 5 (by decide) (by decide) with h4348 | h4348
    · rcases m.htr 3 4 5 (by decide) (by decide) with h4349 | h4349
      · rcases h0bigk with h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c | h4350c
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h0, hlam, p4350_1]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h3609, hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4113, hlam, p4350_1]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4355 | h4355
          · rcases p4350_3 (m.d 0 2) (by simp) with h4356 | h4356
            · rcases p4350_3 (m.d 0 3) (by simp) with h4357 | h4357
              · rcases p4350_3 (m.d 0 4) (by simp) with h4358 | h4358
                · rcases p4350_3 (m.d 0 5) (by simp) with h4359 | h4359
                  · linarith only [h4333, h4359, hlam]
                  · rcases h0emin with h4361 | h4361 | h4361 | h4361 | h4361
                    · linarith only [h4113, h4340, h4343, h4361, hc12, hlam, ht01]
                    · rcases h2bigk with h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c | h4363c
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h0, hlam, p4363_1]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4363_1]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        rcases p4363_3 (m.d 0 2) (by simp) with h4367 | h4367
                        · rcases p4363_3 (m.d 1 2) (by simp) with h4368 | h4368
                          · rcases p4363_3 (m.d 2 3) (by simp) with h4369 | h4369
                            · linarith only [h4334, h4369, hlam]
                            · linarith only [h4346, h4369, hlam]
                          · linarith only [h4341, h4368, hlam]
                        · linarith only [h4367, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        rcases p4363_3 (m.d 0 2) (by simp) with h4374 | h4374
                        · rcases p4363_3 (m.d 1 2) (by simp) with h4375 | h4375
                          · rcases p4363_3 (m.d 2 3) (by simp) with h4376 | h4376
                            · linarith only [h4334, h4376, hlam]
                            · linarith only [h4347, h4376, hlam]
                          · linarith only [h4342, h4375, hlam]
                        · linarith only [h4374, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4361, hc12, hlam, ht01, p4363_1]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4363_1]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        rcases p4363_3 (m.d 0 2) (by simp) with h4384 | h4384
                        · linarith only [h0, h4384, hlam]
                        · linarith only [h4335, h4384, hlam]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h0, h4333, h4342, hlam, p4350_1, p4363_2]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4334, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4340, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4363_1]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        rcases p4363_3 (m.d 0 2) (by simp) with h4392 | h4392
                        · rcases p4363_3 (m.d 1 2) (by simp) with h4393 | h4393
                          · rcases p4363_3 (m.d 2 3) (by simp) with h4394 | h4394
                            · rcases p4363_3 (m.d 2 4) (by simp) with h4395 | h4395
                              · linarith only [h4346, h4395, hlam]
                              · linarith only [h4348, h4395, hlam]
                            · linarith only [h4347, h4394, hlam]
                          · linarith only [h4342, h4393, hlam]
                        · linarith only [h4336, h4392, hlam]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4335, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4341, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4346, hlam, p4363_1]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        rcases p4363_3 (m.d 0 2) (by simp) with h4405 | h4405
                        · rcases p4363_3 (m.d 1 2) (by simp) with h4406 | h4406
                          · rcases p4363_3 (m.d 2 3) (by simp) with h4407 | h4407
                            · rcases p4363_3 (m.d 2 4) (by simp) with h4408 | h4408
                              · rcases p4363_3 (m.d 2 5) (by simp) with h4409 | h4409
                                · linarith only [h4348, h4409, hlam]
                                · rcases h3bigk with h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c | h4411c
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h3609, hlam, p4411_1]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4346, h4349, hc03, hc45, hlam, hphi, ht0b, ht5b, p4411_1]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    rcases p4411_3 (m.d 0 3) (by simp) with h4415 | h4415
                                    · rcases p4411_3 (m.d 1 3) (by simp) with h4416 | h4416
                                      · rcases p4411_3 (m.d 2 3) (by simp) with h4417 | h4417
                                        · linarith only [h4334, h4417, hlam]
                                        · linarith only [h4346, h4417, hlam]
                                      · linarith only [h4343, h4416, hlam]
                                    · linarith only [h4415, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    rcases p4411_3 (m.d 0 3) (by simp) with h4422 | h4422
                                    · rcases p4411_3 (m.d 1 3) (by simp) with h4423 | h4423
                                      · rcases p4411_3 (m.d 2 3) (by simp) with h4424 | h4424
                                        · linarith only [h4334, h4424, hlam]
                                        · linarith only [h4347, h4424, hlam]
                                      · linarith only [h4344, h4423, hlam]
                                    · linarith only [h4422, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h3609, h4333, h4340, h4342, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4350_1, p4411_1]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4340, h4346, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4363_1, p4411_1]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    rcases p4411_3 (m.d 0 3) (by simp) with h4432 | h4432
                                    · linarith only [h3609, h4432, hlam]
                                    · linarith only [h4337, h4432, hlam]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h3609, h4333, h4342, h4347, hlam, p4350_1, p4411_2]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4334, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4340, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h0, h4334, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4411_1]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    rcases p4411_3 (m.d 0 3) (by simp) with h4440 | h4440
                                    · rcases p4411_3 (m.d 1 3) (by simp) with h4441 | h4441
                                      · rcases p4411_3 (m.d 2 3) (by simp) with h4442 | h4442
                                        · rcases p4411_3 (m.d 3 4) (by simp) with h4443 | h4443
                                          · linarith only [h4346, h4443, hlam]
                                          · linarith only [h4349, h4443, hlam]
                                        · linarith only [h4442, hlam, p4411_0]
                                      · linarith only [h4344, h4441, hlam]
                                    · linarith only [h4338, h4440, hlam]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4337, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4343, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4346, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4411_1]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4338, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4344, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4347, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [h4349, hlam, p4411_0]
                                  · have p4411_0 := h4411c.1
                                    have p4411_1 := h4411c.2.1
                                    have p4411_2 := h4411c.2.2.1
                                    have p4411_3 := h4411c.2.2.2
                                    linarith only [hlam, p4411_0]
                              · linarith only [h4348, h4408, hlam]
                            · linarith only [h4347, h4407, hlam]
                          · linarith only [h4342, h4406, hlam]
                        · linarith only [h4336, h4405, hlam]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4336, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4342, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4347, hlam, p4363_1]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [h4348, hlam, p4363_0]
                      · have p4363_0 := h4363c.1
                        have p4363_1 := h4363c.2.1
                        have p4363_2 := h4363c.2.2.1
                        have p4363_3 := h4363c.2.2.2
                        linarith only [hlam, p4363_0]
                    · rcases h2bigk with h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c | h4468c
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h0, hlam, p4468_1]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h0, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4468_1]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        rcases p4468_3 (m.d 0 2) (by simp) with h4472 | h4472
                        · rcases p4468_3 (m.d 1 2) (by simp) with h4473 | h4473
                          · rcases p4468_3 (m.d 2 3) (by simp) with h4474 | h4474
                            · linarith only [h4334, h4474, hlam]
                            · linarith only [h4346, h4474, hlam]
                          · linarith only [h4341, h4473, hlam]
                        · linarith only [h4472, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        rcases p4468_3 (m.d 0 2) (by simp) with h4479 | h4479
                        · rcases p4468_3 (m.d 1 2) (by simp) with h4480 | h4480
                          · rcases p4468_3 (m.d 2 3) (by simp) with h4481 | h4481
                            · linarith only [h4334, h4481, hlam]
                            · linarith only [h4347, h4481, hlam]
                          · linarith only [h4342, h4480, hlam]
                        · linarith only [h4479, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h0, h4333, h4342, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4350_1, p4468_1]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4468_1]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        rcases p4468_3 (m.d 0 2) (by simp) with h4489 | h4489
                        · linarith only [h0, h4489, hlam]
                        · linarith only [h4335, h4489, hlam]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h0, h4333, h4342, hlam, p4350_1, p4468_2]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4334, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4340, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4468_1]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        rcases p4468_3 (m.d 0 2) (by simp) with h4497 | h4497
                        · rcases p4468_3 (m.d 1 2) (by simp) with h4498 | h4498
                          · rcases p4468_3 (m.d 2 3) (by simp) with h4499 | h4499
                            · rcases p4468_3 (m.d 2 4) (by simp) with h4500 | h4500
                              · linarith only [h4346, h4500, hlam]
                              · linarith only [h4348, h4500, hlam]
                            · linarith only [h4347, h4499, hlam]
                          · linarith only [h4342, h4498, hlam]
                        · linarith only [h4336, h4497, hlam]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4335, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4341, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4346, hlam, p4468_1]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        rcases p4468_3 (m.d 0 2) (by simp) with h4510 | h4510
                        · rcases p4468_3 (m.d 1 2) (by simp) with h4511 | h4511
                          · rcases p4468_3 (m.d 2 3) (by simp) with h4512 | h4512
                            · rcases p4468_3 (m.d 2 4) (by simp) with h4513 | h4513
                              · rcases p4468_3 (m.d 2 5) (by simp) with h4514 | h4514
                                · linarith only [h4348, h4514, hlam]
                                · rcases h3bigk with h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c | h4516c
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h3609, hlam, p4516_1]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4516_1]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    rcases p4516_3 (m.d 0 3) (by simp) with h4520 | h4520
                                    · rcases p4516_3 (m.d 1 3) (by simp) with h4521 | h4521
                                      · rcases p4516_3 (m.d 2 3) (by simp) with h4522 | h4522
                                        · linarith only [h4334, h4522, hlam]
                                        · linarith only [h4346, h4522, hlam]
                                      · linarith only [h4343, h4521, hlam]
                                    · linarith only [h4520, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    rcases p4516_3 (m.d 0 3) (by simp) with h4527 | h4527
                                    · rcases p4516_3 (m.d 1 3) (by simp) with h4528 | h4528
                                      · rcases p4516_3 (m.d 2 3) (by simp) with h4529 | h4529
                                        · linarith only [h4334, h4529, hlam]
                                        · linarith only [h4347, h4529, hlam]
                                      · linarith only [h4344, h4528, hlam]
                                    · linarith only [h4527, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4340, h4361, hc12, hlam, ht01, p4516_1]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4340, h4346, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4468_1, p4516_1]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    rcases p4516_3 (m.d 0 3) (by simp) with h4537 | h4537
                                    · linarith only [h3609, h4537, hlam]
                                    · linarith only [h4337, h4537, hlam]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h3609, h4333, h4342, h4347, hlam, p4350_1, p4516_2]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4334, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4340, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h0, h4334, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4516_1]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    rcases p4516_3 (m.d 0 3) (by simp) with h4545 | h4545
                                    · rcases p4516_3 (m.d 1 3) (by simp) with h4546 | h4546
                                      · rcases p4516_3 (m.d 2 3) (by simp) with h4547 | h4547
                                        · rcases p4516_3 (m.d 3 4) (by simp) with h4548 | h4548
                                          · linarith only [h4346, h4548, hlam]
                                          · linarith only [h4349, h4548, hlam]
                                        · linarith only [h4547, hlam, p4516_0]
                                      · linarith only [h4344, h4546, hlam]
                                    · linarith only [h4338, h4545, hlam]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4337, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4343, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4346, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4516_1]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4338, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4344, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4347, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [h4349, hlam, p4516_0]
                                  · have p4516_0 := h4516c.1
                                    have p4516_1 := h4516c.2.1
                                    have p4516_2 := h4516c.2.2.1
                                    have p4516_3 := h4516c.2.2.2
                                    linarith only [hlam, p4516_0]
                              · linarith only [h4348, h4513, hlam]
                            · linarith only [h4347, h4512, hlam]
                          · linarith only [h4342, h4511, hlam]
                        · linarith only [h4336, h4510, hlam]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4336, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4342, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4347, hlam, p4468_1]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [h4348, hlam, p4468_0]
                      · have p4468_0 := h4468c.1
                        have p4468_1 := h4468c.2.1
                        have p4468_2 := h4468c.2.2.1
                        have p4468_3 := h4468c.2.2.2
                        linarith only [hlam, p4468_0]
                    · rcases h2bigk with h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c | h4573c
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h0, hlam, p4573_1]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h0, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4573_1]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        rcases p4573_3 (m.d 0 2) (by simp) with h4577 | h4577
                        · rcases p4573_3 (m.d 1 2) (by simp) with h4578 | h4578
                          · rcases p4573_3 (m.d 2 3) (by simp) with h4579 | h4579
                            · linarith only [h4334, h4579, hlam]
                            · linarith only [h4346, h4579, hlam]
                          · linarith only [h4341, h4578, hlam]
                        · linarith only [h4577, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        rcases p4573_3 (m.d 0 2) (by simp) with h4584 | h4584
                        · rcases p4573_3 (m.d 1 2) (by simp) with h4585 | h4585
                          · rcases p4573_3 (m.d 2 3) (by simp) with h4586 | h4586
                            · linarith only [h4334, h4586, hlam]
                            · linarith only [h4347, h4586, hlam]
                          · linarith only [h4342, h4585, hlam]
                        · linarith only [h4584, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h0, h4333, h4342, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4350_1, p4573_1]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4573_1]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        rcases p4573_3 (m.d 0 2) (by simp) with h4594 | h4594
                        · linarith only [h0, h4594, hlam]
                        · linarith only [h4335, h4594, hlam]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4113, h4333, h4340, h4342, h4343, hlam, p4350_1, p4573_2]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4334, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4340, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4573_1]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        rcases p4573_3 (m.d 0 2) (by simp) with h4602 | h4602
                        · rcases p4573_3 (m.d 1 2) (by simp) with h4603 | h4603
                          · rcases p4573_3 (m.d 2 3) (by simp) with h4604 | h4604
                            · rcases p4573_3 (m.d 2 4) (by simp) with h4605 | h4605
                              · linarith only [h4346, h4605, hlam]
                              · linarith only [h4348, h4605, hlam]
                            · linarith only [h4347, h4604, hlam]
                          · linarith only [h4342, h4603, hlam]
                        · linarith only [h4336, h4602, hlam]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4335, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4341, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4346, hlam, p4573_1]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        rcases p4573_3 (m.d 0 2) (by simp) with h4615 | h4615
                        · rcases p4573_3 (m.d 1 2) (by simp) with h4616 | h4616
                          · rcases p4573_3 (m.d 2 3) (by simp) with h4617 | h4617
                            · rcases p4573_3 (m.d 2 4) (by simp) with h4618 | h4618
                              · rcases p4573_3 (m.d 2 5) (by simp) with h4619 | h4619
                                · linarith only [h4348, h4619, hlam]
                                · rcases h3bigk with h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h3609, hlam, p4621_1]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4346, h4349, hc03, hc45, hlam, hphi, ht0b, ht5b, p4621_1]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    rcases p4621_3 (m.d 0 3) (by simp) with h4625 | h4625
                                    · rcases p4621_3 (m.d 1 3) (by simp) with h4626 | h4626
                                      · rcases p4621_3 (m.d 2 3) (by simp) with h4627 | h4627
                                        · linarith only [h4334, h4627, hlam]
                                        · linarith only [h4346, h4627, hlam]
                                      · linarith only [h4343, h4626, hlam]
                                    · linarith only [h4625, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    rcases p4621_3 (m.d 0 3) (by simp) with h4632 | h4632
                                    · rcases p4621_3 (m.d 1 3) (by simp) with h4633 | h4633
                                      · rcases p4621_3 (m.d 2 3) (by simp) with h4634 | h4634
                                        · linarith only [h4334, h4634, hlam]
                                        · linarith only [h4347, h4634, hlam]
                                      · linarith only [h4344, h4633, hlam]
                                    · linarith only [h4632, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h3609, h4333, h4342, h4347, h4349, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4350_1, p4621_1]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4340, h4346, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4573_1, p4621_1]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    rcases p4621_3 (m.d 0 3) (by simp) with h4642 | h4642
                                    · linarith only [h3609, h4642, hlam]
                                    · linarith only [h4337, h4642, hlam]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h3609, h4333, h4342, h4347, hlam, p4350_1, p4621_2]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4334, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4340, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h0, h4334, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4621_1]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    rcases p4621_3 (m.d 0 3) (by simp) with h4650 | h4650
                                    · rcases p4621_3 (m.d 1 3) (by simp) with h4651 | h4651
                                      · rcases p4621_3 (m.d 2 3) (by simp) with h4652 | h4652
                                        · rcases p4621_3 (m.d 3 4) (by simp) with h4653 | h4653
                                          · linarith only [h4346, h4653, hlam]
                                          · linarith only [h4349, h4653, hlam]
                                        · linarith only [h4652, hlam, p4621_0]
                                      · linarith only [h4344, h4651, hlam]
                                    · linarith only [h4338, h4650, hlam]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4337, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4343, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4346, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4621_1]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4338, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4344, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4347, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [h4349, hlam, p4621_0]
                                  · have p4621_0 := h4621c.1
                                    have p4621_1 := h4621c.2.1
                                    have p4621_2 := h4621c.2.2.1
                                    have p4621_3 := h4621c.2.2.2
                                    linarith only [hlam, p4621_0]
                              · linarith only [h4348, h4618, hlam]
                            · linarith only [h4347, h4617, hlam]
                          · linarith only [h4342, h4616, hlam]
                        · linarith only [h4336, h4615, hlam]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4336, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4342, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4347, hlam, p4573_1]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [h4348, hlam, p4573_0]
                      · have p4573_0 := h4573c.1
                        have p4573_1 := h4573c.2.1
                        have p4573_2 := h4573c.2.2.1
                        have p4573_3 := h4573c.2.2.2
                        linarith only [hlam, p4573_0]
                    · linarith only [h4361, hc01, hlam, p4350_1]
                · linarith only [h4339, h4358, hlam]
              · linarith only [h4338, h4357, hlam]
            · linarith only [h4336, h4356, hlam]
          · linarith only [h4333, h4355, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4683 | h4683
          · linarith only [h0, h4683, hlam]
          · rcases p4350_3 (m.d 0 2) (by simp) with h4685 | h4685
            · rcases p4350_3 (m.d 0 3) (by simp) with h4686 | h4686
              · linarith only [h4334, h4686, hlam]
              · linarith only [h3609, h4686, hlam]
            · linarith only [h0, h4685, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4350_1]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4692 | h4692
          · linarith only [h0, h4692, hlam]
          · rcases p4350_3 (m.d 0 2) (by simp) with h4694 | h4694
            · rcases p4350_3 (m.d 0 3) (by simp) with h4695 | h4695
              · linarith only [h4334, h4695, hlam]
              · linarith only [h4337, h4695, hlam]
            · linarith only [h4335, h4694, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4699 | h4699
          · linarith only [h0, h4699, hlam]
          · linarith only [h4333, h4699, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4702 | h4702
          · linarith only [h3609, h4702, hlam]
          · rcases p4350_3 (m.d 0 2) (by simp) with h4704 | h4704
            · rcases p4350_3 (m.d 0 3) (by simp) with h4705 | h4705
              · rcases p4350_3 (m.d 0 4) (by simp) with h4706 | h4706
                · linarith only [h4337, h4706, hlam]
                · linarith only [h4113, h4706, hlam]
              · linarith only [h3609, h4705, hlam]
            · linarith only [h0, h4704, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4334, hlam, p4350_1]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4713 | h4713
          · linarith only [h3609, h4713, hlam]
          · rcases p4350_3 (m.d 0 2) (by simp) with h4715 | h4715
            · rcases p4350_3 (m.d 0 3) (by simp) with h4716 | h4716
              · rcases p4350_3 (m.d 0 4) (by simp) with h4717 | h4717
                · linarith only [h4337, h4717, hlam]
                · rcases p4350_3 (m.d 0 5) (by simp) with h4719 | h4719
                  · linarith only [h4338, h4719, hlam]
                  · rcases h0emin with h4721 | h4721 | h4721 | h4721 | h4721
                    · linarith only [h0, h4721, hc12, hlam, ht01]
                    · rcases h2bigk with h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c | h4723c
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h0, hlam, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h0, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        rcases p4723_3 (m.d 0 2) (by simp) with h4727 | h4727
                        · rcases p4723_3 (m.d 1 2) (by simp) with h4728 | h4728
                          · rcases p4723_3 (m.d 2 3) (by simp) with h4729 | h4729
                            · linarith only [h4334, h4729, hlam]
                            · linarith only [h4346, h4729, hlam]
                          · linarith only [h4341, h4728, hlam]
                        · linarith only [h4727, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4113, h4333, h4334, h4342, hlam, p4350_1, p4723_2]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4113, h4334, hc01, hc12, hlam, hphi, p4350_1, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        rcases p4723_3 (m.d 0 2) (by simp) with h4738 | h4738
                        · linarith only [h0, h4738, hlam]
                        · linarith only [h4335, h4738, hlam]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h0, h4113, h4333, h4334, h4342, hlam, p4350_1, p4723_2]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4334, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4340, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        rcases p4723_3 (m.d 0 2) (by simp) with h4746 | h4746
                        · rcases p4723_3 (m.d 1 2) (by simp) with h4747 | h4747
                          · rcases p4723_3 (m.d 2 3) (by simp) with h4748 | h4748
                            · rcases p4723_3 (m.d 2 4) (by simp) with h4749 | h4749
                              · linarith only [h4346, h4749, hlam]
                              · linarith only [h4348, h4749, hlam]
                            · linarith only [h4347, h4748, hlam]
                          · linarith only [h4342, h4747, hlam]
                        · linarith only [h4336, h4746, hlam]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4335, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4341, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4346, hlam, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4335, h4347, h4349, hc03, hc45, hlam, hphi, ht0b, ht5b, p4350_1, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4336, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4342, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4347, hlam, p4723_1]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [h4348, hlam, p4723_0]
                      · have p4723_0 := h4723c.1
                        have p4723_1 := h4723c.2.1
                        have p4723_2 := h4723c.2.2.1
                        have p4723_3 := h4723c.2.2.2
                        linarith only [hlam, p4723_0]
                    · rcases h2bigk with h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h0, hlam, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h0, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        rcases p4765_3 (m.d 0 2) (by simp) with h4769 | h4769
                        · rcases p4765_3 (m.d 1 2) (by simp) with h4770 | h4770
                          · rcases p4765_3 (m.d 2 3) (by simp) with h4771 | h4771
                            · linarith only [h4334, h4771, hlam]
                            · linarith only [h4346, h4771, hlam]
                          · linarith only [h4341, h4770, hlam]
                        · linarith only [h4769, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4113, h4333, h4334, h4342, hlam, p4350_1, p4765_2]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4334, h4721, hc12, hlam, ht01, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        rcases p4765_3 (m.d 0 2) (by simp) with h4780 | h4780
                        · linarith only [h0, h4780, hlam]
                        · linarith only [h4335, h4780, hlam]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h0, h4113, h4333, h4334, h4342, hlam, p4350_1, p4765_2]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4334, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4340, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        rcases p4765_3 (m.d 0 2) (by simp) with h4788 | h4788
                        · rcases p4765_3 (m.d 1 2) (by simp) with h4789 | h4789
                          · rcases p4765_3 (m.d 2 3) (by simp) with h4790 | h4790
                            · rcases p4765_3 (m.d 2 4) (by simp) with h4791 | h4791
                              · linarith only [h4346, h4791, hlam]
                              · linarith only [h4348, h4791, hlam]
                            · linarith only [h4347, h4790, hlam]
                          · linarith only [h4342, h4789, hlam]
                        · linarith only [h4336, h4788, hlam]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4335, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4341, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4346, hlam, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4335, h4347, h4349, hc03, hc45, hlam, hphi, ht0b, ht5b, p4350_1, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4336, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4342, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4347, hlam, p4765_1]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [h4348, hlam, p4765_0]
                      · have p4765_0 := h4765c.1
                        have p4765_1 := h4765c.2.1
                        have p4765_2 := h4765c.2.2.1
                        have p4765_3 := h4765c.2.2.2
                        linarith only [hlam, p4765_0]
                    · linarith only [h4721, hc03, hlam, p4350_1]
                    · linarith only [h4721, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h4337, h4716, hlam]
            · linarith only [h4335, h4715, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4811 | h4811
          · linarith only [h3609, h4811, hlam]
          · linarith only [h4333, h4811, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h4814 | h4814
          · linarith only [h4113, h4814, hlam]
          · rcases p4350_3 (m.d 0 2) (by simp) with h4816 | h4816
            · rcases p4350_3 (m.d 0 3) (by simp) with h4817 | h4817
              · rcases p4350_3 (m.d 0 4) (by simp) with h4818 | h4818
                · rcases p4350_3 (m.d 0 5) (by simp) with h4819 | h4819
                  · linarith only [h4339, h4819, hlam]
                  · rcases h0emin with h4821 | h4821 | h4821 | h4821 | h4821
                    · linarith only [h4113, h4340, h4343, h4821, hc12, hlam, ht01, p4350_1]
                    · rcases h2bigk with h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h0, hlam, p4823_1]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h0, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4823_1]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        rcases p4823_3 (m.d 0 2) (by simp) with h4827 | h4827
                        · rcases p4823_3 (m.d 1 2) (by simp) with h4828 | h4828
                          · rcases p4823_3 (m.d 2 3) (by simp) with h4829 | h4829
                            · linarith only [h4334, h4829, hlam]
                            · linarith only [h4346, h4829, hlam]
                          · linarith only [h4341, h4828, hlam]
                        · linarith only [h4827, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4333, h4335, h4342, hlam, p4350_1, p4823_2]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4821, hc12, hlam, ht01, p4823_1]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4823_1]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        rcases p4823_3 (m.d 0 2) (by simp) with h4838 | h4838
                        · linarith only [h0, h4838, hlam]
                        · linarith only [h4335, h4838, hlam]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4113, h4333, h4340, h4342, h4343, hlam, p4350_1, p4823_2]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4334, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4340, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4823_1]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        rcases p4823_3 (m.d 0 2) (by simp) with h4846 | h4846
                        · rcases p4823_3 (m.d 1 2) (by simp) with h4847 | h4847
                          · rcases p4823_3 (m.d 2 3) (by simp) with h4848 | h4848
                            · rcases p4823_3 (m.d 2 4) (by simp) with h4849 | h4849
                              · linarith only [h4346, h4849, hlam]
                              · linarith only [h4348, h4849, hlam]
                            · linarith only [h4347, h4848, hlam]
                          · linarith only [h4342, h4847, hlam]
                        · linarith only [h4336, h4846, hlam]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4335, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4341, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4346, hlam, p4823_1]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        rcases p4823_3 (m.d 0 2) (by simp) with h4859 | h4859
                        · rcases p4823_3 (m.d 1 2) (by simp) with h4860 | h4860
                          · rcases p4823_3 (m.d 2 3) (by simp) with h4861 | h4861
                            · rcases p4823_3 (m.d 2 4) (by simp) with h4862 | h4862
                              · rcases p4823_3 (m.d 2 5) (by simp) with h4863 | h4863
                                · linarith only [h4348, h4863, hlam]
                                · rcases h3bigk with h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c | h4865c
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h3609, hlam, p4865_1]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h3609, h4340, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4865_1]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    rcases p4865_3 (m.d 0 3) (by simp) with h4869 | h4869
                                    · rcases p4865_3 (m.d 1 3) (by simp) with h4870 | h4870
                                      · rcases p4865_3 (m.d 2 3) (by simp) with h4871 | h4871
                                        · linarith only [h4334, h4871, hlam]
                                        · linarith only [h4346, h4871, hlam]
                                      · linarith only [h4343, h4870, hlam]
                                    · linarith only [h4869, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4333, h4337, h4342, h4347, hlam, p4350_1, p4865_2]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4334, h4340, h4346, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4823_1, p4865_1]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4340, h4346, h4347, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4823_1, p4865_1]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    rcases p4865_3 (m.d 0 3) (by simp) with h4880 | h4880
                                    · linarith only [h3609, h4880, hlam]
                                    · linarith only [h4337, h4880, hlam]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4113, h4333, h4342, h4343, h4347, hlam, p4350_1, p4865_2]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4334, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4340, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h0, h4334, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4865_1]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    rcases p4865_3 (m.d 0 3) (by simp) with h4888 | h4888
                                    · rcases p4865_3 (m.d 1 3) (by simp) with h4889 | h4889
                                      · rcases p4865_3 (m.d 2 3) (by simp) with h4890 | h4890
                                        · rcases p4865_3 (m.d 3 4) (by simp) with h4891 | h4891
                                          · linarith only [h4346, h4891, hlam]
                                          · linarith only [h4349, h4891, hlam]
                                        · linarith only [h4890, hlam, p4865_0]
                                      · linarith only [h4344, h4889, hlam]
                                    · linarith only [h4338, h4888, hlam]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4337, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4343, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4346, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h0, h4334, h4346, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4865_1]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4338, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4344, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4347, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [h4349, hlam, p4865_0]
                                  · have p4865_0 := h4865c.1
                                    have p4865_1 := h4865c.2.1
                                    have p4865_2 := h4865c.2.2.1
                                    have p4865_3 := h4865c.2.2.2
                                    linarith only [hlam, p4865_0]
                              · linarith only [h4348, h4862, hlam]
                            · linarith only [h4347, h4861, hlam]
                          · linarith only [h4342, h4860, hlam]
                        · linarith only [h4336, h4859, hlam]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4336, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4342, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4347, hlam, p4823_1]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [h4348, hlam, p4823_0]
                      · have p4823_0 := h4823c.1
                        have p4823_1 := h4823c.2.1
                        have p4823_2 := h4823c.2.2.1
                        have p4823_3 := h4823c.2.2.2
                        linarith only [hlam, p4823_0]
                    · rcases h2bigk with h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c | h4916c
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h0, hlam, p4916_1]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h0, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4916_1]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        rcases p4916_3 (m.d 0 2) (by simp) with h4920 | h4920
                        · rcases p4916_3 (m.d 1 2) (by simp) with h4921 | h4921
                          · rcases p4916_3 (m.d 2 3) (by simp) with h4922 | h4922
                            · linarith only [h4334, h4922, hlam]
                            · linarith only [h4346, h4922, hlam]
                          · linarith only [h4341, h4921, hlam]
                        · linarith only [h4920, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4333, h4334, h4337, h4342, hlam, p4350_1, p4916_2]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4334, h4337, hc01, hc12, hlam, hphi, p4350_1, p4916_1]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4916_1]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        rcases p4916_3 (m.d 0 2) (by simp) with h4931 | h4931
                        · linarith only [h0, h4931, hlam]
                        · linarith only [h4335, h4931, hlam]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h0, h4333, h4334, h4337, h4342, hlam, p4350_1, p4916_2]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4334, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4340, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p4916_1]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        rcases p4916_3 (m.d 0 2) (by simp) with h4939 | h4939
                        · rcases p4916_3 (m.d 1 2) (by simp) with h4940 | h4940
                          · rcases p4916_3 (m.d 2 3) (by simp) with h4941 | h4941
                            · rcases p4916_3 (m.d 2 4) (by simp) with h4942 | h4942
                              · linarith only [h4346, h4942, hlam]
                              · linarith only [h4348, h4942, hlam]
                            · linarith only [h4347, h4941, hlam]
                          · linarith only [h4342, h4940, hlam]
                        · linarith only [h4336, h4939, hlam]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4335, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4341, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4346, hlam, p4916_1]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        rcases p4916_3 (m.d 0 2) (by simp) with h4952 | h4952
                        · rcases p4916_3 (m.d 1 2) (by simp) with h4953 | h4953
                          · rcases p4916_3 (m.d 2 3) (by simp) with h4954 | h4954
                            · rcases p4916_3 (m.d 2 4) (by simp) with h4955 | h4955
                              · rcases p4916_3 (m.d 2 5) (by simp) with h4956 | h4956
                                · linarith only [h4348, h4956, hlam]
                                · rcases h3bigk with h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c | h4958c
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h3609, hlam, p4958_1]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4958_1]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    rcases p4958_3 (m.d 0 3) (by simp) with h4962 | h4962
                                    · rcases p4958_3 (m.d 1 3) (by simp) with h4963 | h4963
                                      · rcases p4958_3 (m.d 2 3) (by simp) with h4964 | h4964
                                        · linarith only [h4334, h4964, hlam]
                                        · linarith only [h4346, h4964, hlam]
                                      · linarith only [h4343, h4963, hlam]
                                    · linarith only [h4962, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4333, h4337, h4342, h4347, hlam, p4350_1, p4958_2]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4340, h4821, hc12, hlam, ht01, p4958_1]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4340, h4346, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4916_1, p4958_1]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    rcases p4958_3 (m.d 0 3) (by simp) with h4973 | h4973
                                    · linarith only [h3609, h4973, hlam]
                                    · linarith only [h4337, h4973, hlam]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h3609, h4333, h4337, h4342, h4347, hlam, p4350_1, p4958_2]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4334, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4340, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h0, h4334, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4958_1]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    rcases p4958_3 (m.d 0 3) (by simp) with h4981 | h4981
                                    · rcases p4958_3 (m.d 1 3) (by simp) with h4982 | h4982
                                      · rcases p4958_3 (m.d 2 3) (by simp) with h4983 | h4983
                                        · rcases p4958_3 (m.d 3 4) (by simp) with h4984 | h4984
                                          · linarith only [h4346, h4984, hlam]
                                          · linarith only [h4349, h4984, hlam]
                                        · linarith only [h4983, hlam, p4958_0]
                                      · linarith only [h4344, h4982, hlam]
                                    · linarith only [h4338, h4981, hlam]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4337, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4343, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4346, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4958_1]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4338, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4344, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4347, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [h4349, hlam, p4958_0]
                                  · have p4958_0 := h4958c.1
                                    have p4958_1 := h4958c.2.1
                                    have p4958_2 := h4958c.2.2.1
                                    have p4958_3 := h4958c.2.2.2
                                    linarith only [hlam, p4958_0]
                              · linarith only [h4348, h4955, hlam]
                            · linarith only [h4347, h4954, hlam]
                          · linarith only [h4342, h4953, hlam]
                        · linarith only [h4336, h4952, hlam]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4336, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4342, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4347, hlam, p4916_1]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [h4348, hlam, p4916_0]
                      · have p4916_0 := h4916c.1
                        have p4916_1 := h4916c.2.1
                        have p4916_2 := h4916c.2.2.1
                        have p4916_3 := h4916c.2.2.2
                        linarith only [hlam, p4916_0]
                    · rcases h2bigk with h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c | h5009c
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h0, hlam, p5009_1]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h0, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5009_1]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        rcases p5009_3 (m.d 0 2) (by simp) with h5013 | h5013
                        · rcases p5009_3 (m.d 1 2) (by simp) with h5014 | h5014
                          · rcases p5009_3 (m.d 2 3) (by simp) with h5015 | h5015
                            · linarith only [h4334, h5015, hlam]
                            · linarith only [h4346, h5015, hlam]
                          · linarith only [h4341, h5014, hlam]
                        · linarith only [h5013, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4333, h4334, h4337, h4342, hlam, p4350_1, p5009_2]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5009_1]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5009_1]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        rcases p5009_3 (m.d 0 2) (by simp) with h5024 | h5024
                        · linarith only [h0, h5024, hlam]
                        · linarith only [h4335, h5024, hlam]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h0, h4333, h4334, h4337, h4342, hlam, p4350_1, p5009_2]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4334, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4340, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4334, h4346, h4349, hc02, hc45, hlam, hphi, ht0b, ht5b, p5009_1]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        rcases p5009_3 (m.d 0 2) (by simp) with h5032 | h5032
                        · rcases p5009_3 (m.d 1 2) (by simp) with h5033 | h5033
                          · rcases p5009_3 (m.d 2 3) (by simp) with h5034 | h5034
                            · rcases p5009_3 (m.d 2 4) (by simp) with h5035 | h5035
                              · linarith only [h4346, h5035, hlam]
                              · linarith only [h4348, h5035, hlam]
                            · linarith only [h4347, h5034, hlam]
                          · linarith only [h4342, h5033, hlam]
                        · linarith only [h4336, h5032, hlam]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4335, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4341, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4346, hlam, p5009_1]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        rcases p5009_3 (m.d 0 2) (by simp) with h5045 | h5045
                        · rcases p5009_3 (m.d 1 2) (by simp) with h5046 | h5046
                          · rcases p5009_3 (m.d 2 3) (by simp) with h5047 | h5047
                            · rcases p5009_3 (m.d 2 4) (by simp) with h5048 | h5048
                              · rcases p5009_3 (m.d 2 5) (by simp) with h5049 | h5049
                                · linarith only [h4348, h5049, hlam]
                                · rcases h3bigk with h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c | h5051c
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h3609, hlam, p5051_1]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4346, h4349, hc03, hc45, hlam, hphi, ht0b, ht5b, p5051_1]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    rcases p5051_3 (m.d 0 3) (by simp) with h5055 | h5055
                                    · rcases p5051_3 (m.d 1 3) (by simp) with h5056 | h5056
                                      · rcases p5051_3 (m.d 2 3) (by simp) with h5057 | h5057
                                        · linarith only [h4334, h5057, hlam]
                                        · linarith only [h4346, h5057, hlam]
                                      · linarith only [h4343, h5056, hlam]
                                    · linarith only [h5055, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4333, h4337, h4342, h4347, hlam, p4350_1, p5051_2]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4334, h4340, h4346, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5009_1, p5051_1]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4340, h4346, h4347, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5009_1, p5051_1]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    rcases p5051_3 (m.d 0 3) (by simp) with h5066 | h5066
                                    · linarith only [h3609, h5066, hlam]
                                    · linarith only [h4337, h5066, hlam]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h3609, h4333, h4337, h4342, h4347, hlam, p4350_1, p5051_2]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4334, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4340, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h0, h4334, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5051_1]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    rcases p5051_3 (m.d 0 3) (by simp) with h5074 | h5074
                                    · rcases p5051_3 (m.d 1 3) (by simp) with h5075 | h5075
                                      · rcases p5051_3 (m.d 2 3) (by simp) with h5076 | h5076
                                        · rcases p5051_3 (m.d 3 4) (by simp) with h5077 | h5077
                                          · linarith only [h4346, h5077, hlam]
                                          · linarith only [h4349, h5077, hlam]
                                        · linarith only [h5076, hlam, p5051_0]
                                      · linarith only [h4344, h5075, hlam]
                                    · linarith only [h4338, h5074, hlam]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4337, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4343, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4346, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h0, h4334, h4346, h4349, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5051_1]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4338, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4344, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4347, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [h4349, hlam, p5051_0]
                                  · have p5051_0 := h5051c.1
                                    have p5051_1 := h5051c.2.1
                                    have p5051_2 := h5051c.2.2.1
                                    have p5051_3 := h5051c.2.2.2
                                    linarith only [hlam, p5051_0]
                              · linarith only [h4348, h5048, hlam]
                            · linarith only [h4347, h5047, hlam]
                          · linarith only [h4342, h5046, hlam]
                        · linarith only [h4336, h5045, hlam]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4336, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4342, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4347, hlam, p5009_1]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [h4348, hlam, p5009_0]
                      · have p5009_0 := h5009c.1
                        have p5009_1 := h5009c.2.1
                        have p5009_2 := h5009c.2.2.1
                        have p5009_3 := h5009c.2.2.2
                        linarith only [hlam, p5009_0]
                    · linarith only [h4821, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h4113, h4818, hlam]
              · linarith only [h3609, h4817, hlam]
            · linarith only [h0, h4816, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4335, hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4337, hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          rcases p4350_3 (m.d 0 1) (by simp) with h5109 | h5109
          · linarith only [h4113, h5109, hlam]
          · linarith only [h4333, h5109, hlam]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4333, hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4336, hlam, p4350_1]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4338, hlam, p4350_0]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [h4339, hlam, p4350_1]
        · have p4350_0 := h4350c.1
          have p4350_1 := h4350c.2.1
          have p4350_2 := h4350c.2.2.1
          have p4350_3 := h4350c.2.2.2
          linarith only [hlam, p4350_0]
      · linarith only [h4349, hc34, hlam, hphi, ht45, u5elo4]
    · linarith only [h4345, h4348, hc24, hlam, hphi, ht45, u5elo1]
  · linarith only [h4347, hc23, hlam, hphi, ht34, ht45, u5elo3]

end R2N4
