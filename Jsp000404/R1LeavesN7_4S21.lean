import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S20

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 0 3 5 (by decide) (by decide) with h16367 | h16367
  · rcases m.htr 0 4 5 (by decide) (by decide) with h16368 | h16368
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16369 | h16369
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16370 | h16370
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16371 | h16371
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16372 | h16372
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16373 | h16373
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16374 | h16374
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16375 | h16375
                  · linarith only [h14856, h14858, h16375, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16377 | h16377
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16378 | h16378
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16379 | h16379
                        · rcases h1bigk with h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c | h16380c
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h0, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h11385, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h12794, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h13812, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            rcases p16380_3 (m.d 0 1) (by simp) with h16386 | h16386
                            · linarith only [h16386, hlam, p16380_0]
                            · rcases p16380_3 (m.d 1 2) (by simp) with h16388 | h16388
                              · rcases p16380_3 (m.d 1 3) (by simp) with h16389 | h16389
                                · linarith only [h16369, h16389, hlam]
                                · linarith only [h11385, h16389, hlam]
                              · linarith only [h16388, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h14856, h14858, h16372, h16377, h16379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h12794, hc01, hc12, hlam, hphi, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            rcases p16380_3 (m.d 0 1) (by simp) with h16397 | h16397
                            · linarith only [h16397, hlam, p16380_0]
                            · rcases p16380_3 (m.d 1 2) (by simp) with h16399 | h16399
                              · rcases p16380_3 (m.d 1 3) (by simp) with h16400 | h16400
                                · rcases p16380_3 (m.d 1 4) (by simp) with h16401 | h16401
                                  · linarith only [h16372, h16401, hlam]
                                  · linarith only [h12794, h16401, hlam]
                                · linarith only [h16400, hlam, p16380_0]
                              · linarith only [h0, h16399, hlam]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h16369, hlam, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h14856, h14858, h16372, h16377, h16379, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h13812, h16369, hc01, hc12, hlam, hphi, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            rcases p16380_3 (m.d 0 1) (by simp) with h16410 | h16410
                            · linarith only [h16410, hlam, p16380_0]
                            · rcases p16380_3 (m.d 1 2) (by simp) with h16412 | h16412
                              · rcases p16380_3 (m.d 1 3) (by simp) with h16413 | h16413
                                · rcases p16380_3 (m.d 1 4) (by simp) with h16414 | h16414
                                  · rcases p16380_3 (m.d 1 5) (by simp) with h16415 | h16415
                                    · linarith only [h16374, h16415, hlam]
                                    · linarith only [h13812, h16415, hlam]
                                  · linarith only [h16414, hlam, p16380_0]
                                · linarith only [h11385, h16413, hlam]
                              · linarith only [h0, h16412, hlam]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h16370, hlam, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h16372, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h13812, hc01, hc14, hlam, hphi, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            rcases p16380_3 (m.d 0 1) (by simp) with h16425 | h16425
                            · linarith only [h16425, hlam, p16380_0]
                            · rcases p16380_3 (m.d 1 2) (by simp) with h16427 | h16427
                              · rcases p16380_3 (m.d 1 3) (by simp) with h16428 | h16428
                                · rcases p16380_3 (m.d 1 4) (by simp) with h16429 | h16429
                                  · rcases p16380_3 (m.d 1 5) (by simp) with h16430 | h16430
                                    · rcases h3bigk with h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c | h16431c
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h11385, hlam, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16377, h16379, hc03, hc45, hlam, hphi, ht0b, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h14858, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h14858, h16379, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h11385, h16369, hc01, hc12, hlam, hphi, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16369, h16377, h16379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h14856, h14858, h16369, h16377, h16379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        rcases p16431_3 (m.d 0 3) (by simp) with h16441 | h16441
                                        · linarith only [h11385, h16441, hlam]
                                        · linarith only [h16367, h16441, hlam]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h14856, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16369, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16375, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h0, h14856, h16379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16369, h16372, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16372, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16369, h16372, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16369, h16372, h16379, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16431_1]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16367, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16373, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16377, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [h16379, hlam, p16431_0]
                                      · have p16431_0 := h16431c.1
                                        have p16431_1 := h16431c.2.1
                                        have p16431_2 := h16431c.2.2.1
                                        have p16431_3 := h16431c.2.2.2
                                        linarith only [hlam, p16431_0]
                                    · linarith only [h16430, hlam, p16380_0]
                                  · linarith only [h12794, h16429, hlam]
                                · linarith only [h11385, h16428, hlam]
                              · linarith only [h0, h16427, hlam]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h16371, hlam, p16380_1]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h16373, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [h16374, hlam, p16380_0]
                          · have p16380_0 := h16380c.1
                            have p16380_1 := h16380c.2.1
                            have p16380_2 := h16380c.2.2.1
                            have p16380_3 := h16380c.2.2.2
                            linarith only [hlam, p16380_0]
                        · linarith only [h14856, h14858, h16368, h16377, h16379, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h14858, h16367, h16368, h16369, h16372, h16375, h16377, h16378, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h14858, h16367, h16369, h16372, h16377, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h12794, h14858, h16367, h16368, h16369, h16372, h16374, hc01, hc12, hlam, hphi]
              · linarith only [h14858, h16367, h16372, h16373, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16472 | h16472
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16473 | h16473
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16474 | h16474
                  · linarith only [h13812, h16372, h16472, h16474, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16476 | h16476
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16477 | h16477
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16478 | h16478
                        · rcases h1bigk with h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c | h16479c
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h0, hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h11385, hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h12794, hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h13812, hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            rcases p16479_3 (m.d 0 1) (by simp) with h16485 | h16485
                            · linarith only [h16485, hlam, p16479_0]
                            · rcases p16479_3 (m.d 1 2) (by simp) with h16487 | h16487
                              · rcases p16479_3 (m.d 1 3) (by simp) with h16488 | h16488
                                · linarith only [h16369, h16488, hlam]
                                · linarith only [h11385, h16488, hlam]
                              · linarith only [h16487, hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h13812, h16472, hc01, hc12, hlam, hphi, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h12794, hc01, hc12, hlam, hphi, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16372, hc01, hc34, hlam, hphi, ht12, ht23, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16369, hlam, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16372, hlam, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h13812, hc01, hc13, hlam, hphi, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            rcases p16479_3 (m.d 0 1) (by simp) with h16501 | h16501
                            · linarith only [h16501, hlam, p16479_0]
                            · rcases p16479_3 (m.d 1 2) (by simp) with h16503 | h16503
                              · rcases p16479_3 (m.d 1 3) (by simp) with h16504 | h16504
                                · linarith only [h16372, h16504, hlam]
                                · linarith only [h11385, h16504, hlam]
                              · linarith only [h0, h16503, hlam]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16370, hlam, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h11385, h16372, hc01, hc34, hlam, hphi, ht12, ht23, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h13812, h16372, hc01, hc34, hlam, hphi, ht12, ht23, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16372, h16472, hc01, hc34, hlam, hphi, ht12, ht23, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16371, hlam, p16479_1]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16472, hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [h16473, hlam, p16479_0]
                          · have p16479_0 := h16479c.1
                            have p16479_1 := h16479c.2.1
                            have p16479_2 := h16479c.2.2.1
                            have p16479_3 := h16479c.2.2.2
                            linarith only [hlam, p16479_0]
                        · linarith only [h11385, h16372, h16478, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h16474, h16476, h16477, hlam]
                    · linarith only [h11385, h16367, h16372, h16476, hc23, hc34, hlam, hphi]
                · linarith only [h11385, h12794, h16367, h16368, h16372, h16473, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h11385, h16367, h16472, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16522 | h16522
            · linarith only [h14858, h16367, h16369, h16371, h16522, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16524 | h16524
              · linarith only [h16370, h16371, h16522, h16524, hlam]
              · linarith only [h11385, h16367, h16524, hlam]
        · linarith only [h0, h14857, h16370, hlam]
      · linarith only [h0, h14856, h16369, hlam]
    · linarith only [h14858, h16367, h16368, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h16530 | h16530
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16531 | h16531
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16532 | h16532
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16533 | h16533
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16534 | h16534
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16535 | h16535
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16536 | h16536
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16537 | h16537
                  · linarith only [h0, h11385, h14856, h14858, h16537, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16539 | h16539
                    · linarith only [h14856, h16367, h16539, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16541 | h16541
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16542 | h16542
                        · rcases h1bigk with h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c | h16543c
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h0, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h11385, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h12794, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h13812, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            rcases p16543_3 (m.d 0 1) (by simp) with h16549 | h16549
                            · linarith only [h16549, hlam, p16543_0]
                            · rcases p16543_3 (m.d 1 2) (by simp) with h16551 | h16551
                              · rcases p16543_3 (m.d 1 3) (by simp) with h16552 | h16552
                                · linarith only [h16531, h16552, hlam]
                                · linarith only [h11385, h16552, hlam]
                              · linarith only [h16551, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h11385, h16367, h16534, h16542, hc01, hc12, hlam, hphi, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h11385, h16367, h16535, h16536, hc01, hc12, hlam, hphi, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h11385, h16367, h16535, hc01, hc12, hlam, hphi, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            rcases p16543_3 (m.d 0 1) (by simp) with h16560 | h16560
                            · linarith only [h16560, hlam, p16543_0]
                            · rcases p16543_3 (m.d 1 2) (by simp) with h16562 | h16562
                              · rcases p16543_3 (m.d 1 3) (by simp) with h16563 | h16563
                                · rcases p16543_3 (m.d 1 4) (by simp) with h16564 | h16564
                                  · linarith only [h16534, h16564, hlam]
                                  · linarith only [h12794, h16564, hlam]
                                · linarith only [h16563, hlam, p16543_0]
                              · linarith only [h0, h16562, hlam]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h16531, hlam, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h11385, h16367, h16535, h16536, hc01, hc13, hlam, hphi, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h11385, h16367, h16531, h16535, hc01, hc12, hlam, hphi, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            rcases p16543_3 (m.d 0 1) (by simp) with h16573 | h16573
                            · linarith only [h16573, hlam, p16543_0]
                            · rcases p16543_3 (m.d 1 2) (by simp) with h16575 | h16575
                              · rcases p16543_3 (m.d 1 3) (by simp) with h16576 | h16576
                                · rcases p16543_3 (m.d 1 4) (by simp) with h16577 | h16577
                                  · rcases p16543_3 (m.d 1 5) (by simp) with h16578 | h16578
                                    · linarith only [h16536, h16578, hlam]
                                    · linarith only [h13812, h16578, hlam]
                                  · linarith only [h16577, hlam, p16543_0]
                                · linarith only [h11385, h16576, hlam]
                              · linarith only [h0, h16575, hlam]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h16532, hlam, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h16534, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h11385, h16367, h16535, hc01, hc14, hlam, hphi, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            rcases p16543_3 (m.d 0 1) (by simp) with h16588 | h16588
                            · linarith only [h16588, hlam, p16543_0]
                            · rcases p16543_3 (m.d 1 2) (by simp) with h16590 | h16590
                              · rcases p16543_3 (m.d 1 3) (by simp) with h16591 | h16591
                                · rcases p16543_3 (m.d 1 4) (by simp) with h16592 | h16592
                                  · rcases p16543_3 (m.d 1 5) (by simp) with h16593 | h16593
                                    · rcases h3bigk with h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c | h16594c
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h11385, hlam, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16367, h16542, hc23, hc34, hlam, hphi, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h14858, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16367, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h11385, h16531, hc01, hc12, hlam, hphi, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        rcases p16594_3 (m.d 0 3) (by simp) with h16602 | h16602
                                        · linarith only [h11385, h16602, hlam]
                                        · linarith only [h14856, h16602, hlam]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h11385, h14858, h16531, hc01, hc12, hlam, hphi, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h11385, h16367, h16531, hc01, hc12, hlam, hphi, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h14856, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16531, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16537, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16539, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h11385, hc01, hc34, hlam, hphi, ht12, ht23, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16534, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16531, h16534, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h11385, h16367, h16531, h16534, hc01, hc12, hlam, hphi, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h11385, hc01, hc35, hlam, hphi, ht12, ht23, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16535, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16531, h16535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16594_1]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [h16542, hlam, p16594_0]
                                      · have p16594_0 := h16594c.1
                                        have p16594_1 := h16594c.2.1
                                        have p16594_2 := h16594c.2.2.1
                                        have p16594_3 := h16594c.2.2.2
                                        linarith only [hlam, p16594_0]
                                    · linarith only [h16593, hlam, p16543_0]
                                  · linarith only [h12794, h16592, hlam]
                                · linarith only [h11385, h16591, hlam]
                              · linarith only [h0, h16590, hlam]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h16533, hlam, p16543_1]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h16535, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [h16536, hlam, p16543_0]
                          · have p16543_0 := h16543c.1
                            have p16543_1 := h16543c.2.1
                            have p16543_2 := h16543c.2.2.1
                            have p16543_3 := h16543c.2.2.2
                            linarith only [hlam, p16543_0]
                        · linarith only [h11385, h14858, h16541, h16542, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16631 | h16631
                        · rcases h1bigk with h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c | h16632c
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h0, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h11385, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h12794, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h13812, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            rcases p16632_3 (m.d 0 1) (by simp) with h16638 | h16638
                            · linarith only [h16638, hlam, p16632_0]
                            · rcases p16632_3 (m.d 1 2) (by simp) with h16640 | h16640
                              · rcases p16632_3 (m.d 1 3) (by simp) with h16641 | h16641
                                · linarith only [h16531, h16641, hlam]
                                · linarith only [h11385, h16641, hlam]
                              · linarith only [h16640, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h12794, h16530, h16541, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            rcases p16632_3 (m.d 0 1) (by simp) with h16649 | h16649
                            · linarith only [h16649, hlam, p16632_0]
                            · rcases p16632_3 (m.d 1 2) (by simp) with h16651 | h16651
                              · rcases p16632_3 (m.d 1 3) (by simp) with h16652 | h16652
                                · rcases p16632_3 (m.d 1 4) (by simp) with h16653 | h16653
                                  · linarith only [h16534, h16653, hlam]
                                  · linarith only [h12794, h16653, hlam]
                                · linarith only [h16652, hlam, p16632_0]
                              · linarith only [h0, h16651, hlam]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h16531, hlam, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h14858, h16530, h16534, h16537, h16541, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h11385, h16367, h16531, h16535, hc01, hc12, hlam, hphi, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            rcases p16632_3 (m.d 0 1) (by simp) with h16662 | h16662
                            · linarith only [h16662, hlam, p16632_0]
                            · rcases p16632_3 (m.d 1 2) (by simp) with h16664 | h16664
                              · rcases p16632_3 (m.d 1 3) (by simp) with h16665 | h16665
                                · rcases p16632_3 (m.d 1 4) (by simp) with h16666 | h16666
                                  · rcases p16632_3 (m.d 1 5) (by simp) with h16667 | h16667
                                    · linarith only [h16536, h16667, hlam]
                                    · linarith only [h13812, h16667, hlam]
                                  · linarith only [h16666, hlam, p16632_0]
                                · linarith only [h11385, h16665, hlam]
                              · linarith only [h0, h16664, hlam]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h16532, hlam, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h16534, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h11385, h16367, h16535, hc01, hc14, hlam, hphi, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            rcases p16632_3 (m.d 0 1) (by simp) with h16677 | h16677
                            · linarith only [h16677, hlam, p16632_0]
                            · rcases p16632_3 (m.d 1 2) (by simp) with h16679 | h16679
                              · rcases p16632_3 (m.d 1 3) (by simp) with h16680 | h16680
                                · rcases p16632_3 (m.d 1 4) (by simp) with h16681 | h16681
                                  · rcases p16632_3 (m.d 1 5) (by simp) with h16682 | h16682
                                    · rcases h3bigk with h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c | h16683c
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h11385, hlam, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16367, hc23, hc35, hlam, hphi, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h14858, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16367, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h11385, h16531, hc01, hc12, hlam, hphi, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        rcases p16683_3 (m.d 0 3) (by simp) with h16691 | h16691
                                        · linarith only [h11385, h16691, hlam]
                                        · linarith only [h14856, h16691, hlam]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h14858, h16530, h16531, h16537, h16541, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h11385, h16367, h16531, hc01, hc12, hlam, hphi, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h14856, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16531, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16537, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16539, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h11385, hc01, hc34, hlam, hphi, ht12, ht23, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16534, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16531, h16534, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h11385, h16367, h16531, h16534, hc01, hc12, hlam, hphi, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h11385, hc01, hc35, hlam, hphi, ht12, ht23, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16535, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16531, h16535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16683_1]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [h16631, hlam, p16683_0]
                                      · have p16683_0 := h16683c.1
                                        have p16683_1 := h16683c.2.1
                                        have p16683_2 := h16683c.2.2.1
                                        have p16683_3 := h16683c.2.2.2
                                        linarith only [hlam, p16683_0]
                                    · linarith only [h16682, hlam, p16632_0]
                                  · linarith only [h12794, h16681, hlam]
                                · linarith only [h11385, h16680, hlam]
                              · linarith only [h0, h16679, hlam]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h16533, hlam, p16632_1]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h16535, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [h16536, hlam, p16632_0]
                          · have p16632_0 := h16632c.1
                            have p16632_1 := h16632c.2.1
                            have p16632_2 := h16632c.2.2.1
                            have p16632_3 := h16632c.2.2.2
                            linarith only [hlam, p16632_0]
                        · linarith only [h14858, h16530, h16631, hlam]
                · linarith only [h12794, h14858, h16530, h16531, h16534, h16536, hc01, hc12, hlam, hphi]
              · linarith only [h11385, h14858, h16534, h16535, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16722 | h16722
              · linarith only [h11385, h16367, h16534, h16722, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16724 | h16724
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16725 | h16725
                  · linarith only [h11385, h16534, h16725, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16727 | h16727
                    · linarith only [h11385, h16722, h16727, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16729 | h16729
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16730 | h16730
                        · rcases h1bigk with h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c | h16731c
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h0, hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h11385, hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h12794, hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h13812, hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            rcases p16731_3 (m.d 0 1) (by simp) with h16737 | h16737
                            · linarith only [h16737, hlam, p16731_0]
                            · rcases p16731_3 (m.d 1 2) (by simp) with h16739 | h16739
                              · rcases p16731_3 (m.d 1 3) (by simp) with h16740 | h16740
                                · linarith only [h16531, h16740, hlam]
                                · linarith only [h11385, h16740, hlam]
                              · linarith only [h16739, hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h12794, hc01, hc12, hlam, hphi, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h16722, h16730, hc01, hc34, hlam, hphi, ht12, ht23, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h16531, hlam, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h16534, hlam, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h16722, hlam, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            rcases p16731_3 (m.d 0 1) (by simp) with h16753 | h16753
                            · linarith only [h16753, hlam, p16731_0]
                            · rcases p16731_3 (m.d 1 2) (by simp) with h16755 | h16755
                              · rcases p16731_3 (m.d 1 3) (by simp) with h16756 | h16756
                                · linarith only [h16534, h16756, hlam]
                                · linarith only [h11385, h16756, hlam]
                              · linarith only [h0, h16755, hlam]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h16532, hlam, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h11385, hc01, hc14, hlam, hphi, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h11385, h16534, h16722, hc01, hc34, hlam, hphi, ht12, ht23, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            rcases p16731_3 (m.d 0 1) (by simp) with h16764 | h16764
                            · linarith only [h16764, hlam, p16731_0]
                            · rcases p16731_3 (m.d 1 2) (by simp) with h16766 | h16766
                              · rcases p16731_3 (m.d 1 3) (by simp) with h16767 | h16767
                                · linarith only [h16722, h16767, hlam]
                                · linarith only [h11385, h16767, hlam]
                              · linarith only [h0, h16766, hlam]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h16533, hlam, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h11385, hc01, hc15, hlam, hphi, p16731_1]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [h16724, hlam, p16731_0]
                          · have p16731_0 := h16731c.1
                            have p16731_1 := h16731c.2.1
                            have p16731_2 := h16731c.2.2.1
                            have p16731_3 := h16731c.2.2.2
                            linarith only [hlam, p16731_0]
                        · linarith only [h0, h12794, h14857, h16534, h16729, h16730, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16776 | h16776
                        · rcases h1bigk with h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c | h16777c
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h0, hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h11385, hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h12794, hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h13812, hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            rcases p16777_3 (m.d 0 1) (by simp) with h16783 | h16783
                            · linarith only [h16783, hlam, p16777_0]
                            · rcases p16777_3 (m.d 1 2) (by simp) with h16785 | h16785
                              · rcases p16777_3 (m.d 1 3) (by simp) with h16786 | h16786
                                · linarith only [h16531, h16786, hlam]
                                · linarith only [h11385, h16786, hlam]
                              · linarith only [h16785, hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h12794, h16530, h16729, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h16534, hc01, hc34, hlam, hphi, ht12, ht23, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h16531, hlam, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h16534, hlam, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h16722, hlam, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            rcases p16777_3 (m.d 0 1) (by simp) with h16799 | h16799
                            · linarith only [h16799, hlam, p16777_0]
                            · rcases p16777_3 (m.d 1 2) (by simp) with h16801 | h16801
                              · rcases p16777_3 (m.d 1 3) (by simp) with h16802 | h16802
                                · linarith only [h16534, h16802, hlam]
                                · linarith only [h11385, h16802, hlam]
                              · linarith only [h0, h16801, hlam]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h16532, hlam, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h11385, hc01, hc14, hlam, hphi, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h13812, h16530, h16534, h16725, h16729, hc23, hc34, hlam, hphi, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            rcases p16777_3 (m.d 0 1) (by simp) with h16810 | h16810
                            · linarith only [h16810, hlam, p16777_0]
                            · rcases p16777_3 (m.d 1 2) (by simp) with h16812 | h16812
                              · rcases p16777_3 (m.d 1 3) (by simp) with h16813 | h16813
                                · linarith only [h16722, h16813, hlam]
                                · linarith only [h11385, h16813, hlam]
                              · linarith only [h0, h16812, hlam]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h16533, hlam, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h11385, hc01, hc15, hlam, hphi, p16777_1]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [h16724, hlam, p16777_0]
                          · have p16777_0 := h16777c.1
                            have p16777_1 := h16777c.2.1
                            have p16777_2 := h16777c.2.2.1
                            have p16777_3 := h16777c.2.2.2
                            linarith only [hlam, p16777_0]
                        · linarith only [h12794, h16530, h16534, h16776, hlam]
                · linarith only [h12794, h16530, h16724, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16823 | h16823
            · linarith only [h11385, h14858, h16531, h16533, h16823, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16825 | h16825
              · linarith only [h11385, h16367, h16823, h16825, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16827 | h16827
                · linarith only [h16532, h16533, h16827, hlam]
                · linarith only [h12794, h16530, h16827, hlam]
        · linarith only [h0, h14857, h16532, hlam]
      · linarith only [h0, h14856, h16531, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16832 | h16832
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16833 | h16833
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16834 | h16834
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16835 | h16835
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16836 | h16836
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16837 | h16837
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16838 | h16838
                  · linarith only [h0, h11385, h14856, h14858, h16838, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16840 | h16840
                    · linarith only [h14856, h16367, h16840, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16842 | h16842
                      · linarith only [h14857, h16530, h16842, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16844 | h16844
                        · linarith only [h12794, h16530, h16832, h16835, h16844, hc01, hc12, hlam, hphi]
                        · linarith only [h11385, h14858, h16832, h16835, h16837, h16844, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16847 | h16847
                  · linarith only [h14856, h14858, h16847, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16849 | h16849
                    · linarith only [h14856, h16367, h16849, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16851 | h16851
                      · linarith only [h12794, h16837, h16851, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16853 | h16853
                        · linarith only [h16835, h16837, h16853, hlam]
                        · rcases h1bigk with h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c | h16855c
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h0, hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h11385, hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h12794, hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h13812, hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            rcases p16855_3 (m.d 0 1) (by simp) with h16861 | h16861
                            · linarith only [h16861, hlam, p16855_0]
                            · rcases p16855_3 (m.d 1 2) (by simp) with h16863 | h16863
                              · rcases p16855_3 (m.d 1 3) (by simp) with h16864 | h16864
                                · linarith only [h16832, h16864, hlam]
                                · linarith only [h11385, h16864, hlam]
                              · linarith only [h16863, hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h12794, hc01, hc12, hlam, hphi, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            rcases p16855_3 (m.d 0 1) (by simp) with h16872 | h16872
                            · linarith only [h16872, hlam, p16855_0]
                            · rcases p16855_3 (m.d 1 2) (by simp) with h16874 | h16874
                              · rcases p16855_3 (m.d 1 3) (by simp) with h16875 | h16875
                                · rcases p16855_3 (m.d 1 4) (by simp) with h16876 | h16876
                                  · linarith only [h16835, h16876, hlam]
                                  · linarith only [h12794, h16876, hlam]
                                · linarith only [h16875, hlam, p16855_0]
                              · linarith only [h0, h16874, hlam]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h16832, hlam, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h11385, h14858, h16835, hc01, hc13, hlam, hphi, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h13812, h16832, hc01, hc12, hlam, hphi, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h16837, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h16833, hlam, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h16835, hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h16837, hlam, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            rcases p16855_3 (m.d 0 1) (by simp) with h16890 | h16890
                            · linarith only [h16890, hlam, p16855_0]
                            · rcases p16855_3 (m.d 1 2) (by simp) with h16892 | h16892
                              · rcases p16855_3 (m.d 1 3) (by simp) with h16893 | h16893
                                · rcases p16855_3 (m.d 1 4) (by simp) with h16894 | h16894
                                  · linarith only [h16837, h16894, hlam]
                                  · linarith only [h12794, h16894, hlam]
                                · linarith only [h11385, h16893, hlam]
                              · linarith only [h0, h16892, hlam]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h16834, hlam, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h16836, hlam, p16855_0]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [h12794, hc01, hc15, hlam, hphi, p16855_1]
                          · have p16855_0 := h16855c.1
                            have p16855_1 := h16855c.2.1
                            have p16855_2 := h16855c.2.2.1
                            have p16855_3 := h16855c.2.2.2
                            linarith only [hlam, p16855_0]
              · linarith only [h11385, h14858, h16835, h16836, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16904 | h16904
              · linarith only [h11385, h16367, h16835, h16904, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16906 | h16906
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16907 | h16907
                  · linarith only [h11385, h16835, h16907, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16909 | h16909
                    · linarith only [h14856, h16367, h16909, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16911 | h16911
                      · linarith only [h14857, h16530, h16911, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16913 | h16913
                        · rcases h1bigk with h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c | h16914c
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h0, hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h11385, hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h12794, hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h13812, hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            rcases p16914_3 (m.d 0 1) (by simp) with h16920 | h16920
                            · linarith only [h16920, hlam, p16914_0]
                            · rcases p16914_3 (m.d 1 2) (by simp) with h16922 | h16922
                              · rcases p16914_3 (m.d 1 3) (by simp) with h16923 | h16923
                                · linarith only [h16832, h16923, hlam]
                                · linarith only [h11385, h16923, hlam]
                              · linarith only [h16922, hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16530, h16906, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16835, hc01, hc34, hlam, hphi, ht12, ht23, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16832, hlam, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16835, hlam, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16904, hlam, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            rcases p16914_3 (m.d 0 1) (by simp) with h16936 | h16936
                            · linarith only [h16936, hlam, p16914_0]
                            · rcases p16914_3 (m.d 1 2) (by simp) with h16938 | h16938
                              · rcases p16914_3 (m.d 1 3) (by simp) with h16939 | h16939
                                · linarith only [h16835, h16939, hlam]
                                · linarith only [h11385, h16939, hlam]
                              · linarith only [h0, h16938, hlam]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16833, hlam, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h11385, hc01, hc14, hlam, hphi, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h11385, h16835, h16904, hc01, hc34, hlam, hphi, ht12, ht23, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            rcases p16914_3 (m.d 0 1) (by simp) with h16947 | h16947
                            · linarith only [h16947, hlam, p16914_0]
                            · rcases p16914_3 (m.d 1 2) (by simp) with h16949 | h16949
                              · rcases p16914_3 (m.d 1 3) (by simp) with h16950 | h16950
                                · linarith only [h16904, h16950, hlam]
                                · linarith only [h11385, h16950, hlam]
                              · linarith only [h0, h16949, hlam]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16834, hlam, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h11385, hc01, hc15, hlam, hphi, p16914_1]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [h16906, hlam, p16914_0]
                          · have p16914_0 := h16914c.1
                            have p16914_1 := h16914c.2.1
                            have p16914_2 := h16914c.2.2.1
                            have p16914_3 := h16914c.2.2.2
                            linarith only [hlam, p16914_0]
                        · linarith only [h11385, h16835, h16913, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16959 | h16959
                  · linarith only [h11385, h16835, h16959, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16961 | h16961
                    · linarith only [h12794, h13812, h14856, h14858, h16904, h16906, h16961, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16963 | h16963
                      · linarith only [h12794, h14857, h16906, h16963, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16965 | h16965
                        · linarith only [h11385, h16835, h16906, h16965, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h11385, h16835, h16965, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16968 | h16968
            · linarith only [h11385, h14858, h16832, h16834, h16968, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16970 | h16970
              · linarith only [h11385, h16367, h16833, h16834, h16968, h16970, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16972 | h16972
                · linarith only [h12794, h16530, h16833, h16834, h16972, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16974 | h16974
                  · linarith only [h11385, h16968, h16974, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16976 | h16976
                    · linarith only [h11385, h16970, h16976, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16978 | h16978
                      · linarith only [h0, h14857, h14858, h16530, h16834, h16976, h16978, hc03, hc35, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16980 | h16980
                        · linarith only [h0, h16834, h16978, h16980, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h11385, h16968, h16980, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h14857, h16833, hlam]
      · linarith only [h0, h14856, h16832, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 0 3 4 (by decide) (by decide) with h14858 | h14858
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858
  · exact r1l7_11_23_L_I_H_I_s15_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858

end R2N4
