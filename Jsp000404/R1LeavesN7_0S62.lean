import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S61

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 66372000 in
set_option maxHeartbeats 66372000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s1 m hb1 hb2 hb4 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h32339 | h32339
    · rcases m.htr 0 1 5 (by decide) (by decide) with h32340 | h32340
      · rcases m.htr 0 2 3 (by decide) (by decide) with h32341 | h32341
        · linarith only [h0, h1, h32341, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h32343 | h32343
          · rcases m.htr 0 2 5 (by decide) (by decide) with h32344 | h32344
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32345 | h32345
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32346 | h32346
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32347 | h32347
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32348 | h32348
                    · linarith only [h0, h1, h32341, h32343, h32348, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32350 | h32350
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32351 | h32351
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32352 | h32352
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32353 | h32353
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32354 | h32354
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32355 | h32355
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32356 | h32356
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32357 | h32357
                                    · linarith only [h0, h1, h32348, h32350, h32357, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h0, h1, h32348, h32350, h32354, h32357, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h1, h32348, h32356, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h32348, h32355, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32362 | h32362
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32363 | h32363
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32364 | h32364
                                    · linarith only [h0, h1, h32348, h32350, h32354, h32364, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32366 | h32366
                                      · linarith only [h32350, h32354, h32362, h32366, hlam]
                                      · rcases h1bigk with h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c | h32368c
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h1, h32348, hc12, hc23, hlam, hphi, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h1, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          rcases p32368_3 (m.d 0 1) (by simp) with h32372 | h32372
                                          · rcases p32368_3 (m.d 1 2) (by simp) with h32373 | h32373
                                            · linarith only [h0, h32373, hlam]
                                            · linarith only [h32350, h32373, hlam]
                                          · linarith only [h32372, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          rcases p32368_3 (m.d 0 1) (by simp) with h32377 | h32377
                                          · rcases p32368_3 (m.d 1 2) (by simp) with h32378 | h32378
                                            · linarith only [h0, h32378, hlam]
                                            · linarith only [h32351, h32378, hlam]
                                          · linarith only [h32377, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h0, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32348, hlam, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h0, h1, h32348, h32350, h32362, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h0, h1, h32348, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h0, h32348, hc12, hc23, hlam, hphi, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          rcases p32368_3 (m.d 0 1) (by simp) with h32388 | h32388
                                          · linarith only [h1, h32388, hlam]
                                          · linarith only [h0, h32388, hlam]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h0, h1, h32343, h32347, h32354, hlam, p32368_2]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          rcases p32368_3 (m.d 0 1) (by simp) with h32393 | h32393
                                          · linarith only [h1, h32393, hlam]
                                          · linarith only [h32340, h32393, hlam]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32339, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32350, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32352, hlam, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32354, hlam, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32340, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32351, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h32353, hlam, p32368_0]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [h1, h32340, h32350, h32362, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p32368_1]
                                        · have p32368_0 := h32368c.1
                                          have p32368_1 := h32368c.2.1
                                          have p32368_2 := h32368c.2.2.1
                                          have p32368_3 := h32368c.2.2.2
                                          linarith only [hlam, p32368_0]
                                  · linarith only [h0, h1, h32348, h32363, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h32343, h32347, h32348, h32354, h32362, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h32350, h32353, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h32350, h32352, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h32344, h32350, h32351, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h32343, h32348, h32350, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32412 | h32412
                    · linarith only [h0, h1, h32341, h32412, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32414 | h32414
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32415 | h32415
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32416 | h32416
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32417 | h32417
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32418 | h32418
                              · linarith only [h32339, h32347, h32418, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32420 | h32420
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32421 | h32421
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32422 | h32422
                                    · linarith only [h32339, h32347, h32414, h32422, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32424 | h32424
                                      · linarith only [h32339, h32347, h32414, h32420, h32424, hlam]
                                      · rcases h1bigk with h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c | h32426c
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h1, h32412, h32415, h32420, h32422, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h1, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          rcases p32426_3 (m.d 0 1) (by simp) with h32430 | h32430
                                          · rcases p32426_3 (m.d 1 2) (by simp) with h32431 | h32431
                                            · linarith only [h0, h32431, hlam]
                                            · linarith only [h32414, h32431, hlam]
                                          · linarith only [h32430, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          rcases p32426_3 (m.d 0 1) (by simp) with h32435 | h32435
                                          · rcases p32426_3 (m.d 1 2) (by simp) with h32436 | h32436
                                            · linarith only [h0, h32436, hlam]
                                            · linarith only [h32415, h32436, hlam]
                                          · linarith only [h32435, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h0, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32412, hlam, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h0, h1, h32412, h32414, h32420, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h0, h1, h32412, h32414, h32418, h32420, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h0, h32412, hc12, hc23, hlam, hphi, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          rcases p32426_3 (m.d 0 1) (by simp) with h32446 | h32446
                                          · linarith only [h1, h32446, hlam]
                                          · linarith only [h0, h32446, hlam]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          rcases p32426_3 (m.d 0 1) (by simp) with h32450 | h32450
                                          · linarith only [h1, h32450, hlam]
                                          · linarith only [h32339, h32450, hlam]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          rcases p32426_3 (m.d 0 1) (by simp) with h32453 | h32453
                                          · linarith only [h1, h32453, hlam]
                                          · linarith only [h32340, h32453, hlam]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32339, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32414, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32416, hlam, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32418, hlam, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32340, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32415, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h32417, hlam, p32426_0]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [h1, h32340, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p32426_1]
                                        · have p32426_0 := h32426c.1
                                          have p32426_1 := h32426c.2.1
                                          have p32426_2 := h32426c.2.2.1
                                          have p32426_3 := h32426c.2.2.2
                                          linarith only [hlam, p32426_0]
                                  · linarith only [h0, h1, h32412, h32421, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h32412, h32414, h32420, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h32414, h32417, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h32414, h32416, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h32344, h32414, h32415, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h32343, h32412, h32414, hc12, hc23, hlam, hphi]
                · linarith only [h1, h32340, h32346, hlam]
              · linarith only [h1, h32339, h32345, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32474 | h32474
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32475 | h32475
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32476 | h32476
                  · linarith only [h32343, h32344, h32476, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32478 | h32478
                    · linarith only [h0, h1, h32341, h32478, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32480 | h32480
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32481 | h32481
                        · linarith only [h0, h32344, h32481, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32483 | h32483
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32484 | h32484
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32485 | h32485
                              · linarith only [h32339, h32476, h32485, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32487 | h32487
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32488 | h32488
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32489 | h32489
                                    · linarith only [h0, h32344, h32476, h32480, h32489, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32491 | h32491
                                      · linarith only [h0, h32344, h32480, h32487, h32489, h32491, hlam]
                                      · rcases h1bigk with h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c | h32493c
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h1, h32478, hc12, hc23, hlam, hphi, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h1, hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          rcases p32493_3 (m.d 0 1) (by simp) with h32497 | h32497
                                          · rcases p32493_3 (m.d 1 2) (by simp) with h32498 | h32498
                                            · linarith only [h0, h32498, hlam]
                                            · linarith only [h32480, h32498, hlam]
                                          · linarith only [h32497, hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h1, h32478, h32480, h32481, h32487, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h0, hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32478, hlam, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h0, h32344, h32480, h32487, h32489, hc34, hc45, hlam, hphi, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32481, hlam, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h0, h32478, hc12, hc23, hlam, hphi, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          rcases p32493_3 (m.d 0 1) (by simp) with h32509 | h32509
                                          · linarith only [h1, h32509, hlam]
                                          · linarith only [h0, h32509, hlam]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          rcases p32493_3 (m.d 0 1) (by simp) with h32513 | h32513
                                          · linarith only [h1, h32513, hlam]
                                          · linarith only [h32339, h32513, hlam]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          rcases p32493_3 (m.d 0 1) (by simp) with h32516 | h32516
                                          · linarith only [h1, h32516, hlam]
                                          · linarith only [h32340, h32516, hlam]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32339, hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32480, hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32483, hlam, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32485, hlam, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32340, hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32340, h32480, h32487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h32484, hlam, p32493_0]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [h1, h32340, h32478, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32493_1]
                                        · have p32493_0 := h32493c.1
                                          have p32493_1 := h32493c.2.1
                                          have p32493_2 := h32493c.2.2.1
                                          have p32493_3 := h32493c.2.2.2
                                          linarith only [hlam, p32493_0]
                                  · linarith only [h0, h1, h32478, h32480, h32487, h32488, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h1, h32340, h32478, h32480, h32481, h32487, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h32340, h32480, h32481, h32484, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h32340, h32480, h32481, h32483, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h32343, h32478, h32480, hc12, hc23, hlam, hphi]
                · linarith only [h1, h32340, h32475, hlam]
              · linarith only [h1, h32340, h32343, h32344, h32474, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h32536 | h32536
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32537 | h32537
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32538 | h32538
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32539 | h32539
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32540 | h32540
                    · linarith only [h0, h1, h32341, h32540, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32542 | h32542
                      · linarith only [h0, h32343, h32542, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32544 | h32544
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32545 | h32545
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32546 | h32546
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32547 | h32547
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32548 | h32548
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32549 | h32549
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32550 | h32550
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32551 | h32551
                                      · rcases h1bigk with h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c | h32552c
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h1, h32540, h32544, h32549, h32551, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h1, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h1, h32540, h32542, h32544, h32549, h32551, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          rcases p32552_3 (m.d 0 1) (by simp) with h32557 | h32557
                                          · rcases p32552_3 (m.d 1 2) (by simp) with h32558 | h32558
                                            · linarith only [h0, h32558, hlam]
                                            · linarith only [h32544, h32558, hlam]
                                          · linarith only [h32557, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h0, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32540, hlam, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32542, hlam, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h0, h1, h32540, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h0, h32540, hc12, hc23, hlam, hphi, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          rcases p32552_3 (m.d 0 1) (by simp) with h32568 | h32568
                                          · linarith only [h1, h32568, hlam]
                                          · linarith only [h0, h32568, hlam]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          rcases p32552_3 (m.d 0 1) (by simp) with h32572 | h32572
                                          · linarith only [h1, h32572, hlam]
                                          · linarith only [h32339, h32572, hlam]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          rcases p32552_3 (m.d 0 1) (by simp) with h32575 | h32575
                                          · linarith only [h1, h32575, hlam]
                                          · linarith only [h32340, h32575, hlam]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32339, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32339, h32544, h32549, h32551, hc01, hc45, hlam, hphi, ht0b, ht5b, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32545, hlam, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h1, h32339, h32540, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p32552_1]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32340, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32544, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32546, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [h32547, hlam, p32552_0]
                                        · have p32552_0 := h32552c.1
                                          have p32552_1 := h32552c.2.1
                                          have p32552_2 := h32552c.2.2.1
                                          have p32552_3 := h32552c.2.2.2
                                          linarith only [hlam, p32552_0]
                                      · linarith only [h1, h32339, h32540, h32547, h32551, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h32340, h32343, h32547, h32550, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1, h32540, h32544, h32549, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h32339, h32540, h32542, h32544, h32548, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h32339, h32539, h32542, h32544, h32547, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h1, h32544, h32546, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1, h32544, h32545, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h32339, h32343, h32536, h32540, h32544, hc12, hc23, hlam, hphi]
                  · linarith only [h32343, h32536, h32539, hlam]
                · linarith only [h1, h32339, h32343, h32536, h32538, hlam]
              · linarith only [h1, h32339, h32537, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32599 | h32599
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32600 | h32600
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32601 | h32601
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32602 | h32602
                    · linarith only [h0, h1, h32341, h32602, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32604 | h32604
                      · linarith only [h0, h32343, h32604, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32606 | h32606
                        · linarith only [h0, h32536, h32606, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32608 | h32608
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32609 | h32609
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32610 | h32610
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32611 | h32611
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32612 | h32612
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32613 | h32613
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32614 | h32614
                                      · rcases h1bigk with h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c | h32615c
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h1, h32602, hc12, hc23, hlam, hphi, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h1, hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h1, h32602, h32608, h32614, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h1, h32602, h32606, hc12, hc23, hlam, hphi, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h0, hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32602, hlam, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32604, hlam, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32606, hlam, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h0, h32602, hc12, hc23, hlam, hphi, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          rcases p32615_3 (m.d 0 1) (by simp) with h32627 | h32627
                                          · linarith only [h1, h32627, hlam]
                                          · linarith only [h0, h32627, hlam]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          rcases p32615_3 (m.d 0 1) (by simp) with h32631 | h32631
                                          · linarith only [h1, h32631, hlam]
                                          · linarith only [h32339, h32631, hlam]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          rcases p32615_3 (m.d 0 1) (by simp) with h32634 | h32634
                                          · linarith only [h1, h32634, hlam]
                                          · linarith only [h32340, h32634, hlam]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32339, hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h1, h32339, h32602, hc12, hc23, hlam, hphi, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32608, hlam, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h1, h32339, h32602, h32606, hc12, hc23, hlam, hphi, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32340, hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h1, h32340, h32602, hc12, hc23, hlam, hphi, p32615_1]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32609, hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [h32610, hlam, p32615_0]
                                        · have p32615_0 := h32615c.1
                                          have p32615_1 := h32615c.2.1
                                          have p32615_2 := h32615c.2.2.1
                                          have p32615_3 := h32615c.2.2.2
                                          linarith only [hlam, p32615_0]
                                      · linarith only [h1, h32339, h32602, h32610, h32614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h32339, h32602, h32610, h32613, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h32339, h32602, h32610, h32612, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h32339, h32602, h32610, h32611, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h32339, h32601, h32602, h32604, h32610, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h32609, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h32339, h32604, h32608, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32654 | h32654
                    · linarith only [h0, h1, h32341, h32654, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32656 | h32656
                      · linarith only [h0, h1, h32343, h32654, h32656, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32658 | h32658
                        · linarith only [h0, h32343, h32536, h32601, h32658, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32660 | h32660
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32661 | h32661
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32662 | h32662
                              · linarith only [h32339, h32601, h32662, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32664 | h32664
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32665 | h32665
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32666 | h32666
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32667 | h32667
                                      · linarith only [h32339, h32601, h32660, h32667, hlam]
                                      · rcases h1bigk with h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c | h32669c
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h1, h32654, hc12, hc23, hlam, hphi, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h1, hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h1, h32654, h32656, hc12, hc23, hlam, hphi, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h1, h32654, h32658, hc12, hc23, hlam, hphi, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h0, hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32654, hlam, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32656, hlam, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32658, hlam, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h0, h32654, hc12, hc23, hlam, hphi, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          rcases p32669_3 (m.d 0 1) (by simp) with h32681 | h32681
                                          · linarith only [h1, h32681, hlam]
                                          · linarith only [h0, h32681, hlam]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          rcases p32669_3 (m.d 0 1) (by simp) with h32685 | h32685
                                          · linarith only [h1, h32685, hlam]
                                          · linarith only [h32339, h32685, hlam]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          rcases p32669_3 (m.d 0 1) (by simp) with h32688 | h32688
                                          · linarith only [h1, h32688, hlam]
                                          · linarith only [h32340, h32688, hlam]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32339, hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h1, h32340, h32654, h32662, hc12, hc23, hlam, hphi, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32660, hlam, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32662, hlam, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32340, hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h1, h32340, h32654, hc12, hc23, hlam, hphi, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h32661, hlam, p32669_0]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [h1, h32340, h32654, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32669_1]
                                        · have p32669_0 := h32669c.1
                                          have p32669_1 := h32669c.2.1
                                          have p32669_2 := h32669c.2.2.1
                                          have p32669_3 := h32669c.2.2.2
                                          linarith only [hlam, p32669_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32701 | h32701
                                      · linarith only [h0, h32343, h32666, h32701, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h1bigk with h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c | h32703c
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h1, h32654, hc12, hc23, hlam, hphi, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h1, hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h1, h32654, h32656, hc12, hc23, hlam, hphi, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h1, h32654, h32658, hc12, hc23, hlam, hphi, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h0, hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32654, hlam, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32656, hlam, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32658, hlam, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h0, h32654, hc12, hc23, hlam, hphi, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          rcases p32703_3 (m.d 0 1) (by simp) with h32715 | h32715
                                          · linarith only [h1, h32715, hlam]
                                          · linarith only [h0, h32715, hlam]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          rcases p32703_3 (m.d 0 1) (by simp) with h32719 | h32719
                                          · linarith only [h1, h32719, hlam]
                                          · linarith only [h32339, h32719, hlam]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          rcases p32703_3 (m.d 0 1) (by simp) with h32722 | h32722
                                          · linarith only [h1, h32722, hlam]
                                          · linarith only [h32340, h32722, hlam]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32339, hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h1, h32339, h32654, hc12, hc23, hlam, hphi, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32660, hlam, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32662, hlam, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32340, hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h1, h32340, h32654, hc12, hc23, hlam, hphi, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h32661, hlam, p32703_0]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [h1, h32340, h32654, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32703_1]
                                        · have p32703_0 := h32703c.1
                                          have p32703_1 := h32703c.2.1
                                          have p32703_2 := h32703c.2.2.1
                                          have p32703_3 := h32703c.2.2.2
                                          linarith only [hlam, p32703_0]
                                  · linarith only [h1, h32340, h32654, h32661, h32665, hlam]
                                · linarith only [h0, h1, h32654, h32664, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h32339, h32656, h32661, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h32339, h32656, h32660, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h32340, h32600, hlam]
              · linarith only [h1, h32339, h32599, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h32741 | h32741
        · linarith only [h0, h1, h32741, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h32743 | h32743
          · rcases m.htr 0 2 5 (by decide) (by decide) with h32744 | h32744
            · linarith only [h0, h32340, h32744, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32746 | h32746
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32747 | h32747
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32748 | h32748
                  · linarith only [h0, h32340, h32743, h32748, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32750 | h32750
                    · linarith only [h0, h32340, h32741, h32750, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32752 | h32752
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32753 | h32753
                        · linarith only [h0, h32340, h32744, h32753, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32755 | h32755
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32756 | h32756
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32757 | h32757
                              · linarith only [h0, h32339, h32340, h32743, h32748, h32757, hlam]
                              · linarith only [h0, h32340, h32752, h32757, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h1, h32747, h32752, h32756, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1, h32752, h32755, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h32741, h32743, h32752, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32763 | h32763
                  · linarith only [h0, h1, h32743, h32747, h32763, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32765 | h32765
                    · linarith only [h0, h1, h32741, h32765, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32767 | h32767
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32768 | h32768
                        · linarith only [h0, h1, h32744, h32747, h32768, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32770 | h32770
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32771 | h32771
                            · linarith only [h0, h1, h32747, h32765, h32767, h32771, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h32767, h32771, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h32767, h32770, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h32741, h32743, h32767, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h32743, h32746, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h32777 | h32777
            · linarith only [h32339, h32340, h32743, h32777, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32779 | h32779
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32780 | h32780
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32781 | h32781
                  · linarith only [h32339, h32340, h32781, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32783 | h32783
                    · linarith only [h0, h32741, h32783, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32785 | h32785
                      · linarith only [h0, h32743, h32785, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32787 | h32787
                        · linarith only [h0, h32340, h32777, h32787, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32789 | h32789
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32790 | h32790
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32791 | h32791
                              · linarith only [h32339, h32340, h32743, h32781, h32790, h32791, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32793 | h32793
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32794 | h32794
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32795 | h32795
                                    · linarith only [h0, h32340, h32791, h32793, h32795, hc12, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32797 | h32797
                                      · linarith only [h32339, h32340, h32789, h32795, h32797, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · rcases h1bigk with h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c | h32799c
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32340, h32787, h32795, hc12, hc45, hlam, hphi, ht23, ht34, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h1, hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32340, h32787, h32795, hc14, hc45, hlam, hphi, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32340, hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h0, hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32783, hlam, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32785, hlam, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32787, hlam, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h0, h32783, hc12, hc23, hlam, hphi, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          rcases p32799_3 (m.d 0 1) (by simp) with h32811 | h32811
                                          · linarith only [h1, h32811, hlam]
                                          · linarith only [h0, h32811, hlam]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          rcases p32799_3 (m.d 0 1) (by simp) with h32815 | h32815
                                          · linarith only [h1, h32815, hlam]
                                          · linarith only [h32339, h32815, hlam]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32339, h32340, h32783, h32785, hc12, hc23, hlam, hphi, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32339, hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32339, h32340, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32789, hlam, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32791, hlam, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32339, h32787, h32795, hc14, hc45, hlam, hphi, p32799_1]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          rcases p32799_3 (m.d 0 1) (by simp) with h32825 | h32825
                                          · linarith only [h32340, h32825, hlam]
                                          · linarith only [h0, h32825, hlam]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [h32790, hlam, p32799_0]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          rcases p32799_3 (m.d 0 1) (by simp) with h32829 | h32829
                                          · linarith only [h32340, h32829, hlam]
                                          · linarith only [h32339, h32829, hlam]
                                        · have p32799_0 := h32799c.1
                                          have p32799_1 := h32799c.2.1
                                          have p32799_2 := h32799c.2.2.1
                                          have p32799_3 := h32799c.2.2.2
                                          linarith only [hlam, p32799_0]
                                  · linarith only [h1, h32780, h32783, h32794, hlam]
                                · linarith only [h1, h32339, h32783, h32785, h32793, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h32780, h32790, hlam]
                          · linarith only [h1, h32339, h32785, h32789, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32837 | h32837
                  · linarith only [h32339, h32340, h32837, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32839 | h32839
                    · linarith only [h0, h1, h32780, h32839, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32841 | h32841
                      · linarith only [h0, h32743, h32841, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32843 | h32843
                        · linarith only [h0, h32777, h32843, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32845 | h32845
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32846 | h32846
                            · linarith only [h1, h32339, h32780, h32839, h32841, h32846, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h32339, h32841, h32846, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h32339, h32841, h32845, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h32339, h32779, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h32851 | h32851
      · rcases m.htr 0 2 3 (by decide) (by decide) with h32852 | h32852
        · linarith only [h0, h1, h32852, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h32854 | h32854
          · linarith only [h0, h32339, h32854, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h32856 | h32856
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32857 | h32857
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32858 | h32858
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32859 | h32859
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32860 | h32860
                    · linarith only [h0, h1, h32852, h32856, h32860, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32862 | h32862
                      · linarith only [h0, h32339, h32854, h32862, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32864 | h32864
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32865 | h32865
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32866 | h32866
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32867 | h32867
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32868 | h32868
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32869 | h32869
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32870 | h32870
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32871 | h32871
                                      · rcases h1bigk with h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c | h32872c
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32339, h32860, h32864, h32865, h32869, h32871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h1, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32339, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          rcases p32872_3 (m.d 0 1) (by simp) with h32877 | h32877
                                          · rcases p32872_3 (m.d 1 2) (by simp) with h32878 | h32878
                                            · linarith only [h0, h32878, hlam]
                                            · linarith only [h32864, h32878, hlam]
                                          · linarith only [h32877, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h0, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32860, hlam, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32862, hlam, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h0, h32339, h32860, h32865, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h0, h32860, hc12, hc23, hlam, hphi, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          rcases p32872_3 (m.d 0 1) (by simp) with h32888 | h32888
                                          · linarith only [h1, h32888, hlam]
                                          · linarith only [h0, h32888, hlam]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h0, h32339, h32860, h32864, h32869, h32871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          rcases p32872_3 (m.d 0 1) (by simp) with h32893 | h32893
                                          · linarith only [h1, h32893, hlam]
                                          · linarith only [h32851, h32893, hlam]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h0, h32864, h32865, h32869, h32871, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          rcases p32872_3 (m.d 0 1) (by simp) with h32897 | h32897
                                          · linarith only [h32339, h32897, hlam]
                                          · linarith only [h0, h32897, hlam]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32865, hlam, p32872_1]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          rcases p32872_3 (m.d 0 1) (by simp) with h32902 | h32902
                                          · linarith only [h32339, h32902, hlam]
                                          · linarith only [h32851, h32902, hlam]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32851, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32864, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32866, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [h32867, hlam, p32872_0]
                                        · have p32872_0 := h32872c.1
                                          have p32872_1 := h32872c.2.1
                                          have p32872_2 := h32872c.2.2.1
                                          have p32872_3 := h32872c.2.2.2
                                          linarith only [hlam, p32872_0]
                                      · linarith only [h0, h32339, h32860, h32864, h32865, h32870, h32871, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h32339, h32851, h32854, h32865, h32867, h32870, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h32339, h32860, h32864, h32865, h32869, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h32339, h32860, h32864, h32865, h32868, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h32339, h32864, h32867, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h32339, h32864, h32865, h32866, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1, h32857, h32864, h32865, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h32339, h32856, h32862, h32864, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h32339, h32856, h32859, hlam]
                · linarith only [h0, h1, h32856, h32858, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32920 | h32920
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32921 | h32921
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32922 | h32922
                    · linarith only [h0, h1, h32857, h32922, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32924 | h32924
                      · linarith only [h0, h1, h32854, h32857, h32924, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32926 | h32926
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32927 | h32927
                          · linarith only [h0, h1, h32857, h32922, h32926, h32927, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1, h32926, h32927, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h32339, h32856, h32924, h32926, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h1, h32856, h32857, h32921, hlam]
                · linarith only [h0, h1, h32856, h32920, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h32933 | h32933
              · rcases m.htr 0 3 5 (by decide) (by decide) with h32934 | h32934
                · rcases m.htr 0 4 5 (by decide) (by decide) with h32935 | h32935
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32936 | h32936
                    · linarith only [h0, h1, h32852, h32936, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h32938 | h32938
                      · linarith only [h0, h32854, h32938, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h32940 | h32940
                        · linarith only [h0, h32856, h32940, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32942 | h32942
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h32943 | h32943
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h32944 | h32944
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32945 | h32945
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h32946 | h32946
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32947 | h32947
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h32948 | h32948
                                      · rcases h1bigk with h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c | h32949c
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32339, h32936, h32942, hc12, hc23, hlam, hphi, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h1, hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32339, hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32339, h32936, h32940, h32942, hc12, hc23, hlam, hphi, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h0, hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32936, hlam, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32938, hlam, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32940, hlam, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h0, h32936, hc12, hc23, hlam, hphi, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          rcases p32949_3 (m.d 0 1) (by simp) with h32961 | h32961
                                          · linarith only [h1, h32961, hlam]
                                          · linarith only [h0, h32961, hlam]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32339, h32851, h32936, h32940, hc12, hc23, hlam, hphi, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          rcases p32949_3 (m.d 0 1) (by simp) with h32966 | h32966
                                          · linarith only [h1, h32966, hlam]
                                          · linarith only [h32851, h32966, hlam]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32851, h32938, h32940, hc12, hc24, hlam, hphi, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          rcases p32949_3 (m.d 0 1) (by simp) with h32970 | h32970
                                          · linarith only [h32339, h32970, hlam]
                                          · linarith only [h0, h32970, hlam]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32942, hlam, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          rcases p32949_3 (m.d 0 1) (by simp) with h32975 | h32975
                                          · linarith only [h32339, h32975, hlam]
                                          · linarith only [h32851, h32975, hlam]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32851, hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h1, h32851, h32936, hc12, hc23, hlam, hphi, p32949_1]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32943, hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [h32944, hlam, p32949_0]
                                        · have p32949_0 := h32949c.1
                                          have p32949_1 := h32949c.2.1
                                          have p32949_2 := h32949c.2.2.1
                                          have p32949_3 := h32949c.2.2.2
                                          linarith only [hlam, p32949_0]
                                      · rcases h1bigk with h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c | h32983c
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32339, h32936, h32942, hc12, hc23, hlam, hphi, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h1, hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32339, hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32339, h32936, h32940, h32942, hc12, hc23, hlam, hphi, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h0, hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32936, hlam, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32938, hlam, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32940, hlam, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h0, h32936, hc12, hc23, hlam, hphi, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          rcases p32983_3 (m.d 0 1) (by simp) with h32995 | h32995
                                          · linarith only [h1, h32995, hlam]
                                          · linarith only [h0, h32995, hlam]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32339, h32851, h32936, h32944, h32948, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          rcases p32983_3 (m.d 0 1) (by simp) with h33000 | h33000
                                          · linarith only [h1, h33000, hlam]
                                          · linarith only [h32851, h33000, hlam]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32851, h32944, h32948, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          rcases p32983_3 (m.d 0 1) (by simp) with h33004 | h33004
                                          · linarith only [h32339, h33004, hlam]
                                          · linarith only [h0, h33004, hlam]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32942, hlam, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          rcases p32983_3 (m.d 0 1) (by simp) with h33009 | h33009
                                          · linarith only [h32339, h33009, hlam]
                                          · linarith only [h32851, h33009, hlam]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32851, hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h1, h32851, h32936, hc12, hc23, hlam, hphi, p32983_1]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32943, hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [h32944, hlam, p32983_0]
                                        · have p32983_0 := h32983c.1
                                          have p32983_1 := h32983c.2.1
                                          have p32983_2 := h32983c.2.2.1
                                          have p32983_3 := h32983c.2.2.2
                                          linarith only [hlam, p32983_0]
                                    · linarith only [h0, h32339, h32938, h32947, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h32339, h32851, h32938, h32940, h32945, h32946, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h32851, h32936, h32940, h32945, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h32339, h32851, h32940, h32944, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h32339, h32851, h32940, h32942, h32943, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h32851, h32933, h32940, h32942, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h32339, h32851, h32935, hlam]
                · linarith only [h1, h32851, h32934, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h33025 | h33025
                · rcases m.htr 0 4 5 (by decide) (by decide) with h33026 | h33026
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33027 | h33027
                    · linarith only [h0, h1, h32933, h33027, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33029 | h33029
                      · linarith only [h0, h1, h32854, h32933, h33029, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33031 | h33031
                        · linarith only [h0, h1, h32856, h33031, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33033 | h33033
                          · linarith only [h0, h1, h32933, h33027, h33033, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h32851, h33031, h33033, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h32851, h32933, h33026, hlam]
                · linarith only [h1, h32851, h33025, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h33038 | h33038
        · linarith only [h0, h1, h33038, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h33040 | h33040
          · linarith only [h0, h32339, h33040, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h33042 | h33042
            · linarith only [h0, h32851, h33042, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h33044 | h33044
              · rcases m.htr 0 3 5 (by decide) (by decide) with h33045 | h33045
                · rcases m.htr 0 4 5 (by decide) (by decide) with h33046 | h33046
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33047 | h33047
                    · linarith only [h0, h1, h33038, h33047, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33049 | h33049
                      · linarith only [h0, h1, h33040, h33046, h33047, h33049, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33051 | h33051
                        · linarith only [h0, h32851, h33042, h33051, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33053 | h33053
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h33054 | h33054
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h33055 | h33055
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h33056 | h33056
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h33057 | h33057
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h33058 | h33058
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h33059 | h33059
                                      · rcases h1bigk with h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c | h33060c
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h32851, h33047, h33053, h33055, hc12, hc23, hlam, hphi, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h1, hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h32339, hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h32851, hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h0, hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h33047, hlam, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h33049, hlam, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h33051, hlam, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h0, h33047, hc12, hc23, hlam, hphi, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          rcases p33060_3 (m.d 0 1) (by simp) with h33072 | h33072
                                          · linarith only [h1, h33072, hlam]
                                          · linarith only [h0, h33072, hlam]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h0, h32339, h33047, hc12, hc23, hlam, hphi, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h0, h32851, h33047, hc12, hc23, hlam, hphi, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h0, h33049, hc12, hc24, hlam, hphi, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          rcases p33060_3 (m.d 0 1) (by simp) with h33079 | h33079
                                          · linarith only [h32339, h33079, hlam]
                                          · linarith only [h0, h33079, hlam]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h33053, hlam, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h0, h32851, h33047, h33053, hc12, hc23, hlam, hphi, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h0, h33051, hc12, hc25, hlam, hphi, p33060_1]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          rcases p33060_3 (m.d 0 1) (by simp) with h33086 | h33086
                                          · linarith only [h32851, h33086, hlam]
                                          · linarith only [h0, h33086, hlam]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h33054, hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [h33055, hlam, p33060_0]
                                        · have p33060_0 := h33060c.1
                                          have p33060_1 := h33060c.2.1
                                          have p33060_2 := h33060c.2.2.1
                                          have p33060_3 := h33060c.2.2.2
                                          linarith only [hlam, p33060_0]
                                      · rcases h1bigk with h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c | h33092c
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h1, h33047, hc12, hc23, hlam, hphi, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h1, hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h32339, hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h32851, hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h0, hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h33047, hlam, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h33049, hlam, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h33051, hlam, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h0, h33047, hc12, hc23, hlam, hphi, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          rcases p33092_3 (m.d 0 1) (by simp) with h33104 | h33104
                                          · linarith only [h1, h33104, hlam]
                                          · linarith only [h0, h33104, hlam]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h0, h32339, h33047, hc12, hc23, hlam, hphi, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h0, h32851, h33047, hc12, hc23, hlam, hphi, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h0, h33049, h33056, hc12, hc23, hlam, hphi, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          rcases p33092_3 (m.d 0 1) (by simp) with h33111 | h33111
                                          · linarith only [h32339, h33111, hlam]
                                          · linarith only [h0, h33111, hlam]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h33053, hlam, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h0, h32851, h33049, h33056, hc12, hc23, hlam, hphi, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h0, h33051, h33056, h33058, hc12, hc23, hlam, hphi, p33092_1]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          rcases p33092_3 (m.d 0 1) (by simp) with h33118 | h33118
                                          · linarith only [h32851, h33118, hlam]
                                          · linarith only [h0, h33118, hlam]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h33054, hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [h33055, hlam, p33092_0]
                                        · have p33092_0 := h33092c.1
                                          have p33092_1 := h33092c.2.1
                                          have p33092_2 := h33092c.2.2.1
                                          have p33092_3 := h33092c.2.2.2
                                          linarith only [hlam, p33092_0]
                                    · linarith only [h0, h32339, h33044, h33046, h33049, h33058, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1, h33047, h33057, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h33047, h33056, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h32339, h33044, h33046, h33055, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h1, h33054, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h33044, h33053, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33130 | h33130
                    · linarith only [h0, h33038, h33130, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33132 | h33132
                      · linarith only [h0, h32339, h33040, h33132, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33134 | h33134
                        · linarith only [h0, h33042, h33134, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33136 | h33136
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h33137 | h33137
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h33138 | h33138
                              · linarith only [h0, h32339, h33046, h33130, h33136, h33138, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h32339, h33138, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h33137, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h33044, h33136, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h33143 | h33143
                  · linarith only [h33044, h33045, h33143, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33145 | h33145
                    · linarith only [h0, h1, h33045, h33145, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33147 | h33147
                      · linarith only [h0, h32339, h33143, h33147, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33149 | h33149
                        · linarith only [h0, h33042, h33149, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33151 | h33151
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h33152 | h33152
                            · linarith only [h0, h32339, h33044, h33045, h33145, h33152, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h33152, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h33044, h33151, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h33156 | h33156
                · rcases m.htr 0 4 5 (by decide) (by decide) with h33157 | h33157
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33158 | h33158
                    · linarith only [h0, h33038, h33158, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33160 | h33160
                      · linarith only [h0, h33040, h33160, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33162 | h33162
                        · linarith only [h0, h32851, h33042, h33162, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33164 | h33164
                          · linarith only [h0, h32851, h33044, h33156, h33158, h33164, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h33164, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h33044, h33156, h33157, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h33168 | h33168
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33169 | h33169
                    · linarith only [h0, h1, h33156, h33169, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33171 | h33171
                      · linarith only [h0, h33040, h33171, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33173 | h33173
                        · linarith only [h0, h33042, h33173, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33175 | h33175
                          · linarith only [h0, h1, h33044, h33169, h33175, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h33175, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33178 | h33178
                    · linarith only [h0, h1, h33156, h33178, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33180 | h33180
                      · linarith only [h0, h32339, h33168, h33180, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h33182 | h33182
                        · linarith only [h0, h33042, h33182, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h33184 | h33184
                          · linarith only [h0, h1, h33044, h33178, h33184, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h33184, hc12, hc34, hlam, hphi, ht23]

end R2N4
