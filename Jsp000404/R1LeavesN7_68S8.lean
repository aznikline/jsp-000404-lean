import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_R_H_I_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h422 | h422
  · rcases m.htr 0 2 3 (by decide) (by decide) with h423 | h423
    · rcases m.htr 0 2 4 (by decide) (by decide) with h424 | h424
      · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
        · rcases m.htr 0 4 5 (by decide) (by decide) with h426 | h426
          · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
            · rcases m.htr 1 2 4 (by decide) (by decide) with h428 | h428
              · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                · rcases m.htr 1 4 5 (by decide) (by decide) with h430 | h430
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h431 | h431
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h432 | h432
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                        · rcases h4bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h425, h428, h432, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p434_1, u2ehi4]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h422, h432, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p434_1, u2ehi4]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h422, h433, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h422, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h432, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p434_1, u2ehi4]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h422, h433, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h424, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h428, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h433, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h0, h422, h428, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h425, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h429, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h431, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h423, h431, hc02, hc45, hlam, hphi, ht0b, ht5b, p434_1]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h426, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h430, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h432, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [h433, hlam, p434_0]
                          · have p434_0 := h434c.1
                            have p434_1 := h434c.2.1
                            have p434_2 := h434c.2.2.1
                            have p434_3 := h434c.2.2.2
                            linarith only [hlam, p434_0]
                        · linarith only [h0, h422, h430, h433, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h422, h430, h432, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h422, h429, h431, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h422, h426, h428, h430, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h465 | h465
                    · linarith only [h427, h429, h465, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
                        · rcases h4bigk with h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h422, h427, h429, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p469_1, u2ehi2]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h422, h465, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p469_1, u2ehi2]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h422, h427, h429, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p469_1, u2ehi2]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h422, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h465, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p469_1, u2ehi2]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h429, hlam, p469_1]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h424, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h428, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h465, hlam, p469_1]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h424, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h425, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h428, hc34, hlam, hphi, ht23, p469_1, u2ehi3]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h423, h425, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p469_1]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h0, h423, h425, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h426, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h464, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h467, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [h468, hlam, p469_0]
                          · have p469_0 := h469c.1
                            have p469_1 := h469c.2.1
                            have p469_2 := h469c.2.2.1
                            have p469_3 := h469c.2.2.2
                            linarith only [hlam, p469_0]
                        · linarith only [h427, h429, h468, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h422, h464, h465, h467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h422, h426, h428, h464, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h423, h428, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h422, h423, h424, h427, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
            · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
              · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
                  · linarith only [h422, h426, h503, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h506 | h506
                      · linarith only [h422, h426, h501, h506, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h508 | h508
                        · linarith only [h422, h426, h501, h505, h508, hlam]
                        · rcases h4bigk with h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h501, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p510_1, u2ehi3]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h426, hc45, hlam, hphi, ht23, ht34, p510_1, u2ehi3]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h426, hc34, hc45, hlam, hphi, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h426, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h422, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h422, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p510_1, u2ehi3]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h503, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h424, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h501, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h0, h424, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h506, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h425, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h502, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h505, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [h508, hlam, p510_0]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hc14, hc45, hlam, hphi, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hc45, hlam, hphi, ht23, ht34, p510_1, u2ehi3]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hc34, hc45, hlam, hphi, p510_1]
                          · have p510_0 := h510c.1
                            have p510_1 := h510c.2.1
                            have p510_2 := h510c.2.2.1
                            have p510_3 := h510c.2.2.2
                            linarith only [hlam, p510_0]
                    · linarith only [h425, h426, h505, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h425, h426, h500, h502, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h423, h501, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h422, h423, h424, h500, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h540 | h540
          · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
            · rcases m.htr 1 2 4 (by decide) (by decide) with h542 | h542
              · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
                · linarith only [h0, h422, h423, h425, h543, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h545 | h545
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h546 | h546
                    · linarith only [h423, h425, h546, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h548 | h548
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                        · rcases h4bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h541, h543, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p550_1, u2ehi2]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h0, h422, h546, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p550_1, u2ehi2]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h425, hlam, p550_1]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h0, h422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p550_1]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h422, hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h546, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p550_1, u2ehi2]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h543, hlam, p550_1]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h0, h422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p550_1]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h424, hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h542, hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h546, hlam, p550_1]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h0, h424, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p550_1]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h424, hc34, hlam, hphi, ht23, p550_1, u2ehi3]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h542, h548, hc34, hlam, hphi, ht23, p550_1, u2ehi4]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h548, hc34, hlam, hphi, ht23, p550_1, u2ehi4]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            rcases p550_3 (m.d 0 4) (by simp) with h570 | h570
                            · linarith only [h425, h570, hlam]
                            · linarith only [h540, h570, hlam]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h540, hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h545, hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h548, hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [h549, hlam, p550_0]
                          · have p550_0 := h550c.1
                            have p550_1 := h550c.2.1
                            have p550_2 := h550c.2.2.1
                            have p550_3 := h550c.2.2.2
                            linarith only [hlam, p550_0]
                        · linarith only [h423, h425, h549, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h422, h545, h548, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h422, h540, h542, h545, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h423, h542, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h422, h423, h425, h541, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h583 | h583
            · rcases m.htr 1 2 4 (by decide) (by decide) with h584 | h584
              · rcases m.htr 1 3 4 (by decide) (by decide) with h585 | h585
                · linarith only [h0, h422, h423, h425, h585, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                  · linarith only [h422, h540, h587, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                    · linarith only [h423, h425, h589, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h591 | h591
                      · linarith only [h422, h540, h584, h591, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h593 | h593
                        · linarith only [h422, h540, h584, h593, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h423, h425, h593, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h423, h584, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h422, h423, h425, h583, hlam]
      · linarith only [h423, h424, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h599 | h599
      · linarith only [h423, h599, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h422, h599, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h602 | h602
    · rcases m.htr 0 2 4 (by decide) (by decide) with h603 | h603
      · rcases m.htr 0 3 4 (by decide) (by decide) with h604 | h604
        · rcases m.htr 0 4 5 (by decide) (by decide) with h605 | h605
          · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
            · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
              · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
                · rcases m.htr 1 4 5 (by decide) (by decide) with h609 | h609
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h610 | h610
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h611 | h611
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h612 | h612
                        · rcases h4bigk with h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h422, hlam, p613_1]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi3]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h602, h604, h612, hc02, hc45, hlam, hphi, ht0b, ht5b, p613_1]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            rcases p613_3 (m.d 0 4) (by simp) with h618 | h618
                            · rcases p613_3 (m.d 1 4) (by simp) with h619 | h619
                              · rcases p613_3 (m.d 2 4) (by simp) with h620 | h620
                                · linarith only [h603, h620, hlam]
                                · linarith only [h611, h620, hlam]
                              · linarith only [h609, h619, hlam]
                            · linarith only [h618, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h422, h606, h608, hc01, hc12, hlam, hphi, p613_1]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h606, h608, h611, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p613_1, u2ehi4]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h606, h608, h612, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p613_1]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            rcases p613_3 (m.d 0 4) (by simp) with h629 | h629
                            · linarith only [h422, h629, hlam]
                            · linarith only [h605, h629, hlam]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h603, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h607, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h603, h612, hc04, hc45, hlam, hphi, ht0b, ht5b, p613_1]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h0, h602, h610, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p613_1]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h604, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h608, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h610, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h0, h602, h604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p613_1]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h605, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h609, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h611, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [h612, hlam, p613_0]
                          · have p613_0 := h613c.1
                            have p613_1 := h613c.2.1
                            have p613_2 := h613c.2.2.1
                            have p613_3 := h613c.2.2.2
                            linarith only [hlam, p613_0]
                        · rcases h4bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h422, hlam, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h422, h606, h608, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p647_1, u2ehi3]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            rcases p647_3 (m.d 0 4) (by simp) with h651 | h651
                            · rcases p647_3 (m.d 1 4) (by simp) with h652 | h652
                              · rcases p647_3 (m.d 2 4) (by simp) with h653 | h653
                                · linarith only [h603, h653, hlam]
                                · linarith only [h610, h653, hlam]
                              · linarith only [h608, h652, hlam]
                            · linarith only [h604, h651, hlam]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h422, h606, h608, h612, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h422, h606, h608, hc01, hc12, hlam, hphi, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h606, h608, h611, h612, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            rcases p647_3 (m.d 0 4) (by simp) with h662 | h662
                            · linarith only [h422, h662, hlam]
                            · linarith only [h604, h662, hlam]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h606, h608, h612, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h603, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h607, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h0, h603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h0, h602, h610, h612, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h604, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h608, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h610, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h612, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h605, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h609, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [h611, hlam, p647_0]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hc34, hc45, hlam, hphi, p647_1]
                          · have p647_0 := h647c.1
                            have p647_1 := h647c.2.1
                            have p647_2 := h647c.2.2.1
                            have p647_3 := h647c.2.2.2
                            linarith only [hlam, p647_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h681 | h681
                        · linarith only [h611, h681, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases h4bigk with h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h422, hlam, p683_1]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h422, h606, h608, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p683_1, u2ehi3]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            rcases p683_3 (m.d 0 4) (by simp) with h687 | h687
                            · rcases p683_3 (m.d 1 4) (by simp) with h688 | h688
                              · rcases p683_3 (m.d 2 4) (by simp) with h689 | h689
                                · linarith only [h603, h689, hlam]
                                · linarith only [h610, h689, hlam]
                              · linarith only [h608, h688, hlam]
                            · linarith only [h604, h687, hlam]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h422, h606, h608, h611, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p683_1, u2ehi3]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h422, h606, h608, hc01, hc12, hlam, hphi, p683_1]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h606, h608, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p683_1, u2ehi3]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            rcases p683_3 (m.d 0 4) (by simp) with h698 | h698
                            · linarith only [h422, h698, hlam]
                            · linarith only [h604, h698, hlam]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h606, h608, h611, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p683_1, u2ehi3]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h603, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h607, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h605, h611, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p683_1]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h611, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h604, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h608, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h610, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h681, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h605, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h609, hlam, p683_0]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h605, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p683_1]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [h422, h605, h606, h608, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p683_1]
                          · have p683_0 := h683c.1
                            have p683_1 := h683c.2.1
                            have p683_2 := h683c.2.2.1
                            have p683_3 := h683c.2.2.2
                            linarith only [hlam, p683_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h717 | h717
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h718 | h718
                        · rcases h4bigk with h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h422, hlam, p719_1]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h422, h606, h608, h717, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p719_1]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h422, h606, h608, h610, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi2]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            rcases p719_3 (m.d 0 4) (by simp) with h724 | h724
                            · rcases p719_3 (m.d 1 4) (by simp) with h725 | h725
                              · rcases p719_3 (m.d 2 4) (by simp) with h726 | h726
                                · linarith only [h603, h726, hlam]
                                · linarith only [h717, h726, hlam]
                              · linarith only [h609, h725, hlam]
                            · linarith only [h724, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h422, h606, h608, hc01, hc12, hlam, hphi, p719_1]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h606, h608, h610, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi2]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h606, h608, h610, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p719_1, u2ehi2]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            rcases p719_3 (m.d 0 4) (by simp) with h735 | h735
                            · linarith only [h422, h735, hlam]
                            · linarith only [h605, h735, hlam]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h603, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h607, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h610, hlam, p719_1]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h0, h603, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p719_1]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h604, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h608, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p719_1, u2ehi3]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h0, h602, h604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p719_1]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h605, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h609, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h717, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [h718, hlam, p719_0]
                          · have p719_0 := h719c.1
                            have p719_1 := h719c.2.1
                            have p719_2 := h719c.2.2.1
                            have p719_3 := h719c.2.2.2
                            linarith only [hlam, p719_0]
                        · linarith only [h610, h718, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                        · linarith only [h0, h602, h604, h610, h717, h754, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h605, h610, h754, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h422, h602, h604, h605, h609, hc01, hc12, hlam, hphi]
                · linarith only [h422, h604, h608, hlam]
              · linarith only [h0, h602, h607, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h602, h606, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
            · rcases m.htr 1 2 4 (by decide) (by decide) with h762 | h762
              · rcases m.htr 1 3 4 (by decide) (by decide) with h763 | h763
                · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h766 | h766
                      · linarith only [h603, h605, h766, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h768 | h768
                        · linarith only [h602, h603, h605, h765, h768, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases h4bigk with h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c | h770c
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h422, hlam, p770_1]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p770_1, u2ehi3]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h605, h763, h764, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p770_1]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h605, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h422, h763, hc01, hc13, hlam, hphi, p770_1]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h761, h763, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p770_1, u2ehi3]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            rcases p770_3 (m.d 0 4) (by simp) with h779 | h779
                            · linarith only [h422, h779, hlam]
                            · linarith only [h604, h779, hlam]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h603, h605, h761, h763, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p770_1, u2ehi3]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h603, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h762, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h603, h605, hc34, hc45, hlam, hphi, p770_1]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h766, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h604, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h763, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h765, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h768, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p770_1]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h764, hlam, p770_0]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h761, h763, h764, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p770_1, u2ehi3]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [h761, h763, h764, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p770_1]
                          · have p770_0 := h770c.1
                            have p770_1 := h770c.2.1
                            have p770_2 := h770c.2.2.1
                            have p770_3 := h770c.2.2.2
                            linarith only [hlam, p770_0]
                    · linarith only [h604, h605, h761, h763, h764, h765, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h800 | h800
                      · linarith only [h422, h764, h799, h800, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h802 | h802
                        · linarith only [h422, h603, h764, h799, h802, hlam]
                        · rcases h4bigk with h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c | h804c
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h422, hlam, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p804_1, u2ehi3]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h422, h764, hc34, hc45, hlam, hphi, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h605, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h764, hc04, hc45, hlam, hphi, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h764, hc45, hlam, hphi, ht23, ht34, p804_1, u2ehi3]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h764, hc34, hc45, hlam, hphi, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h764, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h603, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h762, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h422, h603, h764, hc34, hc45, hlam, hphi, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h800, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h604, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h763, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h799, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [h802, hlam, p804_0]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hc14, hc45, hlam, hphi, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hc45, hlam, hphi, ht23, ht34, p804_1, u2ehi3]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hc34, hc45, hlam, hphi, p804_1]
                          · have p804_0 := h804c.1
                            have p804_1 := h804c.2.1
                            have p804_2 := h804c.2.2.1
                            have p804_3 := h804c.2.2.2
                            linarith only [hlam, p804_0]
                    · linarith only [h604, h605, h799, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h604, h605, h761, h763, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h602, h762, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h602, h761, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h834 | h834
          · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
            · rcases m.htr 1 2 4 (by decide) (by decide) with h836 | h836
              · rcases m.htr 1 3 4 (by decide) (by decide) with h837 | h837
                · rcases m.htr 1 4 5 (by decide) (by decide) with h838 | h838
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
                    · linarith only [h602, h604, h839, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h841 | h841
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h842 | h842
                        · rcases h4bigk with h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h422, hlam, p843_1]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h839, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p843_1, u2ehi2]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h604, hlam, p843_1]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h604, h835, h837, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p843_1]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h422, hc01, hc14, hlam, hphi, p843_1]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h836, h839, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p843_1, u2ehi2]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h602, h604, h835, h837, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p843_1, u2ehi2]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            rcases p843_3 (m.d 0 4) (by simp) with h853 | h853
                            · linarith only [h422, h853, hlam]
                            · linarith only [h834, h853, hlam]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h603, hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h836, hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h839, hlam, p843_1]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h603, hc02, hc45, hlam, hphi, ht0b, ht5b, p843_1]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h603, hc34, hlam, hphi, ht23, p843_1, u2ehi3]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h837, hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h835, h837, h841, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p843_1, u2ehi4]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h835, h837, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p843_1]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h834, hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h838, hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h841, hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [h842, hlam, p843_0]
                          · have p843_0 := h843c.1
                            have p843_1 := h843c.2.1
                            have p843_2 := h843c.2.2.1
                            have p843_3 := h843c.2.2.2
                            linarith only [hlam, p843_0]
                        · linarith only [h602, h604, h842, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h604, h834, h841, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h422, h604, h834, h835, h837, h838, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h875 | h875
                    · linarith only [h0, h422, h602, h837, h875, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h877 | h877
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h878 | h878
                        · rcases h4bigk with h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h422, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h875, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p879_1, u2ehi2]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h604, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            rcases p879_3 (m.d 0 4) (by simp) with h884 | h884
                            · rcases p879_3 (m.d 1 4) (by simp) with h885 | h885
                              · rcases p879_3 (m.d 2 4) (by simp) with h886 | h886
                                · linarith only [h603, h886, hlam]
                                · linarith only [h877, h886, hlam]
                              · linarith only [h874, h885, hlam]
                            · linarith only [h884, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h422, h837, hc01, hc34, hlam, hphi, ht12, ht23, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h837, h875, hc34, hlam, hphi, ht23, p879_1, u2ehi2]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h837, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            rcases p879_3 (m.d 0 4) (by simp) with h895 | h895
                            · linarith only [h422, h895, hlam]
                            · linarith only [h834, h895, hlam]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h603, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h836, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h875, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h0, h603, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h603, hc34, hlam, hphi, ht23, p879_1, u2ehi3]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h422, hc01, hc34, hlam, hphi, ht12, ht23, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p879_1, u2ehi3]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            rcases p879_3 (m.d 0 4) (by simp) with h907 | h907
                            · linarith only [h604, h907, hlam]
                            · linarith only [h834, h907, hlam]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h834, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h874, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h877, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h878, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                        · linarith only [h602, h604, h878, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h604, h834, h875, h877, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h422, h834, h874, hlam]
              · linarith only [h0, h602, h836, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h602, h835, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h920 | h920
            · rcases m.htr 1 2 4 (by decide) (by decide) with h921 | h921
              · rcases m.htr 1 3 4 (by decide) (by decide) with h922 | h922
                · rcases m.htr 1 4 5 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h924 | h924
                    · linarith only [h602, h604, h924, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
                      · linarith only [h0, h422, h603, h834, h926, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h928 | h928
                        · linarith only [h602, h604, h834, h928, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h602, h604, h920, h922, h923, h928, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h602, h604, h922, h923, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h932 | h932
                  · linarith only [h602, h604, h834, h922, h932, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h934 | h934
                    · linarith only [h602, h604, h934, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h936 | h936
                      · linarith only [h422, h932, h936, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h938 | h938
                        · linarith only [h422, h602, h604, h932, h938, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h602, h604, h938, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h602, h921, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h602, h920, hlam]
      · linarith only [h602, h603, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h944 | h944
      · linarith only [h602, h944, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h946 | h946
        · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
          · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
            · rcases m.htr 1 2 4 (by decide) (by decide) with h949 | h949
              · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h953 | h953
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h954 | h954
                        · rcases h4bigk with h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h422, hlam, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h944, hlam, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h954, hc04, hc45, hlam, hphi, ht0b, ht5b, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h944, h948, h952, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h422, h950, hc01, hc13, hlam, hphi, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h944, h948, h950, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p955_1, u2ehi0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h948, h950, h954, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            rcases p955_3 (m.d 0 4) (by simp) with h965 | h965
                            · linarith only [h422, h965, hlam]
                            · linarith only [h947, h965, hlam]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h944, hc24, hlam, hphi, p955_1, u2ehi0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h949, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h948, h952, h954, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h948, h952, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h946, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h950, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h952, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h946, hc03, hc45, hlam, hphi, ht0b, ht5b, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h947, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h951, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h953, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h954, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                        · rcases h4bigk with h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h422, hlam, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h944, hlam, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h944, h948, h952, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h944, h948, h952, h954, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h422, h948, h950, hc01, hc12, hlam, hphi, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h948, h950, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi3]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            rcases p983_3 (m.d 0 4) (by simp) with h992 | h992
                            · linarith only [h422, h992, hlam]
                            · linarith only [h946, h992, hlam]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h948, h950, h954, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h947, h954, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h949, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h948, h952, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h948, h952, h954, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h946, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h950, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h952, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h954, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h947, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h951, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h953, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h947, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                      · linarith only [h944, h947, h953, hlam]
                    · linarith only [h602, h952, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h422, h602, h946, h947, h948, h951, hc01, hc12, hlam, hphi]
                · linarith only [h602, h946, h948, h950, hlam]
              · linarith only [h602, h948, h949, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1016 | h1016
              · linarith only [h1016, h948, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1018 | h1018
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1019 | h1019
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1020 | h1020
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1021 | h1021
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1022 | h1022
                        · rcases h4bigk with h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c | h1023c
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h422, hlam, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h944, hlam, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1018, h1022, h422, h948, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            rcases p1023_3 (m.d 0 4) (by simp) with h1028 | h1028
                            · rcases p1023_3 (m.d 1 4) (by simp) with h1029 | h1029
                              · rcases p1023_3 (m.d 2 4) (by simp) with h1030 | h1030
                                · rcases p1023_3 (m.d 3 4) (by simp) with h1031 | h1031
                                  · linarith only [h1031, h946, hlam]
                                  · linarith only [h1022, h1031, hlam]
                                · linarith only [h1021, h1030, hlam]
                              · linarith only [h1019, h1029, hlam]
                            · linarith only [h1028, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1018, h422, h948, hc01, hc23, hlam, hphi, ht12, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1016, hlam, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1018, h1022, h948, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            rcases p1023_3 (m.d 0 4) (by simp) with h1041 | h1041
                            · linarith only [h1041, h422, hlam]
                            · linarith only [h1041, h947, hlam]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1020, h944, hc23, hlam, hphi, p1023_1, u2ehi0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1020, h422, hc01, hc23, hlam, hphi, ht12, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1020, h1022, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            rcases p1023_3 (m.d 0 4) (by simp) with h1048 | h1048
                            · linarith only [h1048, h944, hlam]
                            · linarith only [h1048, h947, hlam]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h946, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1018, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1020, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h946, hc03, hc45, hlam, hphi, ht0b, ht5b, p1023_1]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h947, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1019, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1021, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [h1022, hlam, p1023_0]
                          · have p1023_0 := h1023c.1
                            have p1023_1 := h1023c.2.1
                            have p1023_2 := h1023c.2.2.1
                            have p1023_3 := h1023c.2.2.2
                            linarith only [hlam, p1023_0]
                        · rcases h4bigk with h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h422, hlam, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h944, hlam, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            rcases p1061_3 (m.d 0 4) (by simp) with h1065 | h1065
                            · rcases p1061_3 (m.d 1 4) (by simp) with h1066 | h1066
                              · rcases p1061_3 (m.d 2 4) (by simp) with h1067 | h1067
                                · rcases p1061_3 (m.d 3 4) (by simp) with h1068 | h1068
                                  · linarith only [h1068, h946, hlam]
                                  · rcases p1061_3 (m.d 4 5) (by simp) with h1070 | h1070
                                    · linarith only [h1070, h947, hlam]
                                    · linarith only [h1022, h1070, hlam]
                                · linarith only [h1020, h1067, hlam]
                              · linarith only [h1018, h1066, hlam]
                            · linarith only [h1065, h946, hlam]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1022, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h422, hc01, hc14, hlam, hphi, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1016, hlam, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            rcases p1061_3 (m.d 0 4) (by simp) with h1080 | h1080
                            · linarith only [h1080, h422, hlam]
                            · linarith only [h1080, h946, hlam]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1016, h1020, h1022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1020, h1022, h947, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1020, h422, hc01, hc23, hlam, hphi, ht12, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            rcases p1061_3 (m.d 0 4) (by simp) with h1087 | h1087
                            · linarith only [h1087, h944, hlam]
                            · linarith only [h1087, h946, hlam]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1020, h1022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h946, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1018, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1020, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1022, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h947, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1019, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h1021, hlam, p1061_0]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [h947, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1061_1]
                          · have p1061_0 := h1061c.1
                            have p1061_1 := h1061c.2.1
                            have p1061_2 := h1061c.2.2.1
                            have p1061_3 := h1061c.2.2.2
                            linarith only [hlam, p1061_0]
                      · linarith only [h1016, h1021, h422, h947, hlam]
                    · linarith only [h1020, h602, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1019, h422, h947, hlam]
                · linarith only [h0, h1018, h602, h946, h948, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1105 | h1105
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1106 | h1106
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1107 | h1107
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1108 | h1108
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1110 | h1110
                      · linarith only [h1105, h1109, h1110, h944, h947, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1107, h1108, h1110, h944, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1109, h602, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1106, h1108, h944, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · linarith only [h1105, h1107, h602, h946, hlam]
              · linarith only [h1105, h1106, h602, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1117 | h1117
              · linarith only [h1105, h1117, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1119 | h1119
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1120 | h1120
                  · linarith only [h1117, h1120, h944, h947, hc24, hlam, hphi, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1122 | h1122
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1123 | h1123
                      · linarith only [h1117, h1120, h1122, h1123, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1123, h944, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1122, h602, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h0, h1105, h1119, h602, h946, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1128 | h1128
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1129 | h1129
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1130 | h1130
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1131 | h1131
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1132 | h1132
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                    · linarith only [h1129, h1133, h602, h946, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1133, h602, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1128, h1132, h422, hlam]
                · linarith only [h1129, h1131, h602, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h1129, h1130, h602, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1139 | h1139
              · linarith only [h1129, h1139, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1141 | h1141
                · linarith only [h1129, h1141, h602, h946, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1143 | h1143
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1144 | h1144
                    · linarith only [h1144, h602, h946, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1144, h602, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1128, h1143, h422, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1148 | h1148
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1149 | h1149
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1150 | h1150
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1151 | h1151
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1152 | h1152
                    · linarith only [h1148, h1152, h602, h946, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1152, h602, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1149, h1151, h944, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · linarith only [h1148, h1150, h602, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h1148, h1149, h602, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
              · linarith only [h1148, h1158, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1160 | h1160
                · linarith only [h1148, h1160, h602, h946, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1162 | h1162
                  · linarith only [h1128, h1158, h1162, h944, hc24, hlam, hphi, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1164 | h1164
                    · linarith only [h1164, h602, h946, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1164, h602, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
