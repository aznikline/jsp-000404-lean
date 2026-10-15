import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13744000 in
set_option maxHeartbeats 13744000 in
theorem r1l7_13_24_L_I_H_I_s9_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h8811 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h8812 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8813 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  rcases m.htr 0 2 4 (by decide) (by decide) with h9369 | h9369
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9370 | h9370
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9371 | h9371
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9372 | h9372
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9373 | h9373
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9374 | h9374
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9375 | h9375
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9376 | h9376
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9377 | h9377
                  · linarith only [h0, h8811, h8813, h9373, h9377, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h8811, h8813, h9372, h9373, h9377, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h8812, h8813, h9371, h9373, h9376, hc03, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h7360, h9370, h9375, hlam]
            · linarith only [h0, h8811, h9369, h9374, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9383 | h9383
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9384 | h9384
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9385 | h9385
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9386 | h9386
                  · linarith only [h0, h8811, h9373, h9386, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h8811, h9372, h9373, h9384, h9386, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h7360, h9371, h9385, hlam]
              · linarith only [h7360, h9370, h9384, hlam]
            · linarith only [h0, h7360, h8813, h9369, h9383, hc01, hc13, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9392 | h9392
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9393 | h9393
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9394 | h9394
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9395 | h9395
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9396 | h9396
                  · linarith only [h0, h8811, h9372, h9396, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9398 | h9398
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9399 | h9399
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9400 | h9400
                        · linarith only [h8813, h9369, h9372, h9392, h9400, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9402 | h9402
                          · linarith only [h0, h8811, h8813, h9372, h9392, h9393, h9398, h9402, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases h3bigk with h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c | h9404c
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h7360, hlam, p9404_1]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h8813, hlam, p9404_1]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              rcases p9404_3 (m.d 0 3) (by simp) with h9408 | h9408
                              · rcases p9404_3 (m.d 1 3) (by simp) with h9409 | h9409
                                · rcases p9404_3 (m.d 2 3) (by simp) with h9410 | h9410
                                  · rcases p9404_3 (m.d 3 4) (by simp) with h9411 | h9411
                                    · linarith only [h9411, hlam, p9404_0]
                                    · rcases p9404_3 (m.d 3 5) (by simp) with h9413 | h9413
                                      · linarith only [h9371, h9413, hlam]
                                      · linarith only [h9402, h9413, hlam]
                                  · linarith only [h9398, h9410, hlam]
                                · linarith only [h9394, h9409, hlam]
                              · linarith only [h9408, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              rcases p9404_3 (m.d 0 3) (by simp) with h9419 | h9419
                              · rcases p9404_3 (m.d 1 3) (by simp) with h9420 | h9420
                                · rcases p9404_3 (m.d 2 3) (by simp) with h9421 | h9421
                                  · rcases p9404_3 (m.d 3 4) (by simp) with h9422 | h9422
                                    · linarith only [h9370, h9422, hlam]
                                    · rcases p9404_3 (m.d 3 5) (by simp) with h9424 | h9424
                                      · linarith only [h9424, hlam, p9404_0]
                                      · rcases h4bigk with h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c | h9426c
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9372, hc14, hc45, hlam, hphi, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h0, h8812, h8813, h9372, h9392, h9398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h0, h8812, h8813, h9372, h9392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9372, hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h8811, hlam, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h0, h8812, h8813, h9392, h9396, h9398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h0, h8812, h8813, h9392, h9396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9396, hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9369, hlam, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9393, hlam, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h8813, h9369, h9392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9400, hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9370, hlam, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9394, hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9398, hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9402, hlam, p9426_0]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hc14, hc45, hlam, hphi, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [h9398, hc34, hc45, hlam, hphi, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hc34, hc45, hlam, hphi, p9426_1]
                                        · have p9426_0 := h9426c.1
                                          have p9426_1 := h9426c.2.1
                                          have p9426_2 := h9426c.2.2.1
                                          have p9426_3 := h9426c.2.2.2
                                          linarith only [hlam, p9426_0]
                                  · linarith only [h9399, h9421, hlam]
                                · linarith only [h9395, h9420, hlam]
                              · linarith only [h9419, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              rcases p9404_3 (m.d 0 3) (by simp) with h9455 | h9455
                              · linarith only [h7360, h9455, hlam]
                              · rcases p9404_3 (m.d 1 3) (by simp) with h9457 | h9457
                                · rcases p9404_3 (m.d 2 3) (by simp) with h9458 | h9458
                                  · linarith only [h9392, h9458, hlam]
                                  · linarith only [h8813, h9458, hlam]
                                · linarith only [h7360, h9457, hlam]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h0, h8813, h9392, hc01, hc12, hlam, hphi, p9404_1]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              rcases p9404_3 (m.d 0 3) (by simp) with h9464 | h9464
                              · linarith only [h7360, h9464, hlam]
                              · linarith only [h9370, h9464, hlam]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              rcases p9404_3 (m.d 0 3) (by simp) with h9467 | h9467
                              · linarith only [h7360, h9467, hlam]
                              · linarith only [h9371, h9467, hlam]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h0, h8812, h8813, h9392, h9393, h9396, h9398, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9404_1]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9392, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              rcases p9404_3 (m.d 0 3) (by simp) with h9473 | h9473
                              · linarith only [h8813, h9473, hlam]
                              · linarith only [h9370, h9473, hlam]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              rcases p9404_3 (m.d 0 3) (by simp) with h9476 | h9476
                              · linarith only [h8813, h9476, hlam]
                              · linarith only [h9371, h9476, hlam]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9370, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9394, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9398, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9402, hlam, p9404_1]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9371, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9395, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h9399, hlam, p9404_0]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [h8813, h9371, h9392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9404_1]
                            · have p9404_0 := h9404c.1
                              have p9404_1 := h9404c.2.1
                              have p9404_2 := h9404c.2.2.1
                              have p9404_3 := h9404c.2.2.2
                              linarith only [hlam, p9404_0]
                      · linarith only [h7360, h8812, h8813, h9395, h9399, hlam]
                    · linarith only [h0, h8811, h8813, h9370, h9398, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h8813, h9371, h9392, h9395, hlam]
              · linarith only [h8813, h9370, h9392, h9394, hlam]
            · linarith only [h0, h8811, h8813, h9392, h9393, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9494 | h9494
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9495 | h9495
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9496 | h9496
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9497 | h9497
                  · linarith only [h0, h8811, h9392, h9497, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9499 | h9499
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9500 | h9500
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9501 | h9501
                        · linarith only [h0, h8812, h9372, h9392, h9494, h9497, h9501, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9503 | h9503
                          · linarith only [h8811, h9372, h9494, h9499, h9503, hlam]
                          · rcases h3bigk with h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c | h9505c
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h7360, hlam, p9505_1]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h8813, hlam, p9505_1]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              rcases p9505_3 (m.d 0 3) (by simp) with h9509 | h9509
                              · rcases p9505_3 (m.d 1 3) (by simp) with h9510 | h9510
                                · rcases p9505_3 (m.d 2 3) (by simp) with h9511 | h9511
                                  · rcases p9505_3 (m.d 3 4) (by simp) with h9512 | h9512
                                    · linarith only [h9512, hlam, p9505_0]
                                    · rcases p9505_3 (m.d 3 5) (by simp) with h9514 | h9514
                                      · linarith only [h9371, h9514, hlam]
                                      · linarith only [h9503, h9514, hlam]
                                  · linarith only [h9499, h9511, hlam]
                                · linarith only [h9495, h9510, hlam]
                              · linarith only [h9509, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              rcases p9505_3 (m.d 0 3) (by simp) with h9520 | h9520
                              · rcases p9505_3 (m.d 1 3) (by simp) with h9521 | h9521
                                · rcases p9505_3 (m.d 2 3) (by simp) with h9522 | h9522
                                  · rcases p9505_3 (m.d 3 4) (by simp) with h9523 | h9523
                                    · linarith only [h9370, h9523, hlam]
                                    · rcases p9505_3 (m.d 3 5) (by simp) with h9525 | h9525
                                      · linarith only [h9525, hlam, p9505_0]
                                      · rcases h4bigk with h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c | h9527c
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9372, hc14, hc45, hlam, hphi, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h0, h8811, h9499, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h0, h8811, h9392, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9372, hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h8811, hlam, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h0, h8811, h9392, h9499, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h0, h8812, h9392, h9497, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9497, hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9369, hlam, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9494, hlam, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9369, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9501, hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9370, hlam, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9495, hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9499, hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9503, hlam, p9527_0]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9494, hc24, hc45, hlam, hphi, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [h9499, hc34, hc45, hlam, hphi, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [hc34, hc45, hlam, hphi, p9527_1]
                                        · have p9527_0 := h9527c.1
                                          have p9527_1 := h9527c.2.1
                                          have p9527_2 := h9527c.2.2.1
                                          have p9527_3 := h9527c.2.2.2
                                          linarith only [hlam, p9527_0]
                                  · linarith only [h9500, h9522, hlam]
                                · linarith only [h9496, h9521, hlam]
                              · linarith only [h9520, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              rcases p9505_3 (m.d 0 3) (by simp) with h9556 | h9556
                              · linarith only [h7360, h9556, hlam]
                              · rcases p9505_3 (m.d 1 3) (by simp) with h9558 | h9558
                                · rcases p9505_3 (m.d 2 3) (by simp) with h9559 | h9559
                                  · rcases p9505_3 (m.d 3 4) (by simp) with h9560 | h9560
                                    · linarith only [h9495, h9560, hlam]
                                    · rcases p9505_3 (m.d 3 5) (by simp) with h9562 | h9562
                                      · linarith only [h9496, h9562, hlam]
                                      · rcases h4bigk with h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c | h9564c
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h0, h8811, h8813, h9392, h9494, h9499, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9505_1, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h0, h8811, h8813, h9392, h9499, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9505_1, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h0, h8811, h8813, h9392, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9505_1, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9372, hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h8811, hlam, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h0, h8811, h8813, h9392, h9499, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9505_1, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h0, h8811, h8813, h9392, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9505_1, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9497, hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9369, hlam, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9494, hlam, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h8813, h9369, h9392, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9505_1, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9501, hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9370, hlam, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9495, hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9499, hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9503, hlam, p9564_0]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9494, hc24, hc45, hlam, hphi, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [h9499, hc34, hc45, hlam, hphi, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [hc34, hc45, hlam, hphi, p9564_1]
                                        · have p9564_0 := h9564c.1
                                          have p9564_1 := h9564c.2.1
                                          have p9564_2 := h9564c.2.2.1
                                          have p9564_3 := h9564c.2.2.2
                                          linarith only [hlam, p9564_0]
                                  · linarith only [h8813, h9559, hlam]
                                · linarith only [h7360, h9558, hlam]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9392, hlam, p9505_1]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              rcases p9505_3 (m.d 0 3) (by simp) with h9594 | h9594
                              · linarith only [h7360, h9594, hlam]
                              · linarith only [h9370, h9594, hlam]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              rcases p9505_3 (m.d 0 3) (by simp) with h9597 | h9597
                              · linarith only [h7360, h9597, hlam]
                              · linarith only [h9371, h9597, hlam]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              rcases p9505_3 (m.d 0 3) (by simp) with h9600 | h9600
                              · linarith only [h8813, h9600, hlam]
                              · rcases p9505_3 (m.d 1 3) (by simp) with h9602 | h9602
                                · linarith only [h9392, h9602, hlam]
                                · linarith only [h7360, h9602, hlam]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h7360, h8812, h9494, h9497, h9499, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9505_1]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h0, h8812, h9392, h9494, h9497, h9499, hlam, p9505_2]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h0, h8812, h9392, h9496, hlam, p9505_2]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9370, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9495, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9499, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9503, hlam, p9505_1]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9371, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9496, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h9500, hlam, p9505_0]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [h0, h8812, h9496, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9505_1]
                            · have p9505_0 := h9505c.1
                              have p9505_1 := h9505c.2.1
                              have p9505_2 := h9505c.2.2.1
                              have p9505_3 := h9505c.2.2.2
                              linarith only [hlam, p9505_0]
                      · linarith only [h0, h8812, h9392, h9496, h9500, hlam]
                    · linarith only [h0, h8812, h9392, h9499, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h0, h8811, h9371, h9392, h9494, h9496, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h7360, h9370, h9495, hlam]
            · linarith only [h0, h8811, h9369, h9494, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h0, h8812, h8813, h9371, hlam]
    · linarith only [h0, h8811, h8813, h9370, hlam]
  · linarith only [h0, h8811, h9369, hlam]

set_option maxHeartbeats 13744000 in
set_option maxHeartbeats 13744000 in
theorem r1l7_13_24_L_I_H_I_s9_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h8811 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h8812 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  rcases m.htr 0 2 3 (by decide) (by decide) with h8813 | h8813
  · exact r1l7_13_24_L_I_H_I_s9_x0_x0_x0 m hb3 hb4 hg0 hg7360 h8811 h8812 h8813
  · exact r1l7_13_24_L_I_H_I_s9_x0_x0_x1 m hb3 hb4 hg0 hg7360 h8811 h8812 h8813

end R2N4
